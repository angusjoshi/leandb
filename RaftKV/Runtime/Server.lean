import RaftKV.Protocol.Node
import RaftKV.Protocol.Frame
import RaftKV.Storage.LogArray
import RaftKV.Storage.KVHash
import Std.Http
import Std.Async

/-!
# The runtime shim

This is the untrusted, unverified edge of the system, and it is deliberately
thin. Its entire job is:

* turn sockets and timers into `Event`s,
* hand them to the pure `Protocol.step`, and
* execute the `Action`s that come back.

It makes no protocol decisions of its own. Every choice that could threaten
safety — whether to grant a vote, whether to accept entries, when to advance
the commit index — is made inside `step`, where it is proved.
-/

namespace RaftKV.Runtime

open Std Std.Http Std.Async RaftKV RaftKV.Protocol

/-- The concrete replica type: array-backed log, hash-map state machine. -/
abbrev RNode := NodeState ArrayLog HashKV

/-- What a waiting client is eventually told. -/
inductive Outcome where
  /-- The command committed and applied, with this result. -/
  | done (r : Reply)
  /-- This node is not the leader; try `hint`. -/
  | redirect (hint : Option Nat)
  deriving Inhabited, Repr

/-- Everything one running replica needs. -/
structure Node where
  /-- Static cluster configuration. -/
  cfg : Config
  /-- The pure replica state, under a lock. -/
  st : Std.Mutex RNode
  /-- Peer id to its Raft (inter-node) address. -/
  peers : List (Nat × Net.SocketAddress)
  /-- Clients blocked awaiting a committed result. -/
  waiters : Std.Mutex (HashMap Nat (Channel Outcome))
  /-- Source of unique client request ids. -/
  nextReq : IO.Ref Nat
  /-- Set when a leader has been heard from since the last election check. -/
  heard : IO.Ref Bool

/-- Hand an outcome to whoever is waiting on `rid`, if anyone still is. -/
def Node.resolve (nd : Node) (rid : Nat) (o : Outcome) : Async Unit := do
  let w ← nd.waiters.atomically (do pure (← get)[rid]?)
  match w with
  | none => pure ()
  | some ch => discard <| ch.send o

/-- Execute one `Action` produced by `step`. -/
def Node.exec (nd : Node) : Action → Async Unit
  | .reply rid r => nd.resolve rid (.done r)
  | .notLeader rid hint => nd.resolve rid (.redirect hint)
  | .send to msg => do
      match nd.peers.lookup to, Frame.selfCheck msg with
      | some addr, some line =>
          -- Best effort: a peer being down is normal and must not disturb us.
          background do
            try
              let c ← TCP.Socket.Client.mk
              c.connect addr
              c.send s!"{nd.cfg.me} {line}\n".toUTF8
              c.shutdown
            catch _ => pure ()
      | _, none => IO.eprintln s!"[{nd.cfg.me}] codec self-check FAILED; message dropped"
      | none, _ => pure ()

/-- Feed one event to the replica and carry out the consequences. -/
def Node.dispatch (nd : Node) (ev : Event) : Async Unit := do
  let acts ← nd.st.atomically do
    let s ← get
    let (s', acts) := Protocol.step s ev
    set s'
    pure acts
  for a in acts do
    nd.exec a

/-- Submit a client command and wait for it to commit, or be redirected. -/
def Node.submit (nd : Node) (cmd : Command) : Async Outcome := do
  let rid ← nd.nextReq.modifyGet (fun n => (n, n + 1))
  let ch ← Channel.new (capacity := some 1)
  nd.waiters.atomically (modify (·.insert rid ch))
  nd.dispatch (.clientReq rid cmd)
  let o ← Async.ofAsyncTask ((← ch.recv).map Except.ok)
  nd.waiters.atomically (modify (·.erase rid))
  pure o

/-! ## Peer transport -/

/-- Handle one inbound peer line: `<senderId> <framed message>`. -/
def Node.onPeerLine (nd : Node) (line : String) : Async Unit := do
  let line := line.trimAscii.toString
  if line.isEmpty then pure () else
  match line.splitOn " " with
  | [] => pure ()
  | idStr :: rest =>
    match idStr.toNat?, Frame.decodeMsg (" ".intercalate rest) with
    | some src, some msg => do
        match msg with
        | .appendEntries .. => nd.heard.set true
        | _ => pure ()
        nd.dispatch (.recv src msg)
    | _, _ => IO.eprintln s!"[{nd.cfg.me}] undecodable peer line"

/-- Accept loop for inter-node traffic. -/
partial def Node.serveRaft (nd : Node) (addr : Net.SocketAddress) : Async Unit := do
  let sock ← TCP.Socket.Server.mk
  sock.bind addr
  sock.listen 128
  let rec loop : Async Unit := do
    let client ← sock.accept
    background do
      try
        let mut buf := ByteArray.empty
        let mut go := true
        while go do
          match ← client.recv? 65536 with
          | none => go := false
          | some b => buf := buf ++ b
        match String.fromUTF8? buf with
        | none => pure ()
        | some text =>
          for l in text.splitOn "\n" do
            nd.onPeerLine l
      catch _ => pure ()
    loop
  loop

/-! ## Timers -/

/-- Randomised election timeout, so split votes resolve. -/
partial def Node.electionLoop (nd : Node) : Async Unit := do
  let rec loop : Async Unit := do
    let jitter ← IO.rand 300 600
    Async.sleep (Std.Time.Millisecond.Offset.ofNat jitter)
    let heardFromLeader ← nd.heard.modifyGet (fun b => (b, false))
    let isLeader ← nd.st.atomically (do pure ((← get).role == Role.leader))
    if !heardFromLeader && !isLeader then
      nd.dispatch .electionTimeout
    loop
  loop

/-- Leaders refresh their authority regularly. -/
partial def Node.heartbeatLoop (nd : Node) : Async Unit := do
  let rec loop : Async Unit := do
    Async.sleep (Std.Time.Millisecond.Offset.ofNat 80)
    let isLeader ← nd.st.atomically (do pure ((← get).role == Role.leader))
    if isLeader then nd.dispatch .heartbeatTimeout
    loop
  loop

/-! ## Client HTTP API -/

/-- Render an `Outcome` as an HTTP response. -/
def respond (o : Outcome) : Async (Response Body.Full) :=
  match o with
  | .done (.value none) => Response.notFound.text "not found\n"
  | .done (.value (some v)) => Response.ok.text (v ++ "\n")
  | .done .ok => Response.ok.text "ok\n"
  | .redirect hint =>
      (Response.withStatus .serviceUnavailable).text
        (match hint with
         | some l => s!"not leader; try node {l}\n"
         | none => "not leader; no leader known\n")

/-- Split a request path into its non-empty segments. -/
def pathSegments (r : Request.Head) : List String :=
  (toString (r.uri.path)).splitOn "/" |>.filter (· != "")

/-- The client-facing HTTP handler. -/
def Node.httpHandler (nd : Node) : Server.StatelessHandler :=
  Server.Handler.ofFn fun req => do
    let segs := pathSegments req.line
    match req.line.method, segs with
    | .get, ["status"] => do
        let s ← nd.st.atomically (do pure (← get))
        Response.ok.text
          s!"node={s.cfg.me} role={repr s.role} term={s.currentTerm} commit={s.commitIndex} applied={s.lastApplied}\n"
    | .get, ["kv", k] => do respond (← nd.submit (.get k))
    | .delete, ["kv", k] => do respond (← nd.submit (.del k))
    | .put, ["kv", k] => do
        let body : ByteArray ← Body.Stream.readAll req.body
        match String.fromUTF8? body with
        | none => Response.badRequest.text "body is not valid UTF-8\n"
        | some v => do respond (← nd.submit (.put k v.trimAscii.toString))
    | _, _ => Response.notFound.text "usage: GET|PUT|DELETE /kv/<key>, GET /status\n"

/-- Build a replica. -/
def Node.create (cfg : Config) (peers : List (Nat × Net.SocketAddress)) : IO Node := do
  let st ← Std.Mutex.new (Protocol.initState (σ := ArrayLog) (κ := HashKV) cfg)
  let waiters ← Std.Mutex.new (∅ : HashMap Nat (Channel Outcome))
  let nextReq ← IO.mkRef 1
  let heard ← IO.mkRef false
  pure { cfg, st, peers, waiters, nextReq, heard }

/-- Start every loop and serve until shutdown. -/
def Node.run (nd : Node) (raftAddr httpAddr : Net.SocketAddress) : Async Unit := do
  background (nd.serveRaft raftAddr)
  background nd.electionLoop
  background nd.heartbeatLoop
  let srv ← Server.serve httpAddr nd.httpHandler
  IO.println s!"[node {nd.cfg.me}] raft={raftAddr} http={httpAddr}"
  srv.waitShutdown

end RaftKV.Runtime
