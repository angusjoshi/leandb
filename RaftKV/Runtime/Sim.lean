import RaftKV.Protocol.Node
import RaftKV.Storage.LogArray
import RaftKV.Storage.KVHash

/-!
# Deterministic simulator

Because `step` is pure, a whole cluster can be run in one process with no
sockets and no clock, and any schedule replays exactly. This is the harness for
finding protocol bugs cheaply, and later for randomised schedule testing with
injected partitions and crashes.

It is *not* part of the trusted path — it is a testing tool built on the same
`step` the real server uses.
-/

namespace RaftKV.Sim

open RaftKV Protocol

/-- Concrete node state used by the simulator. -/
abbrev SNode := NodeState ArrayLog HashKV

/-- A cluster plus the network's in-flight messages. -/
structure World where
  /-- Replica states, indexed by node id. -/
  nodes : Array SNode
  /-- Messages in flight, as `(src, dst, msg)`. -/
  inflight : List (Nat × Nat × Msg)
  /-- Client replies observed so far, newest last. -/
  replies : List (Nat × Reply)
  /-- Requests that were refused, newest last. -/
  refused : List Nat
  /--
  Every `(index, entry)` any node has *ever* applied.

  A restart resets `lastApplied` to zero, so a check that only inspects the
  final states cannot see anything applied before a crash. This history is the
  durable form of the observation, and is what the safety checks use.
  -/
  applied : List (Nat × Entry)
  /-- Every `(voter, term, candidate)` vote ever granted on the wire. -/
  votes : List (Nat × Nat × Nat)
  /-- Every `(log index, request id, reply)` ever returned to a client. -/
  answered : List (Nat × Nat × Reply)
  deriving Inhabited

/-- Build an `n`-node cluster with empty logs. -/
def World.init (n : Nat) : World :=
  { nodes := (List.range n).toArray.map (fun i =>
      Protocol.initState { me := i, members := List.range n })
    inflight := [], replies := [], refused := [],
    applied := [], votes := [], answered := [] }

/-- Route one node's emitted actions into the world. -/
def World.absorb (w : World) (me : Nat) (acts : List Action) : World :=
  acts.foldl (fun w a =>
    match a with
    | .send to (.requestVoteResp t true) =>
        { w with inflight := w.inflight ++ [(me, to, Msg.requestVoteResp t true)],
                 votes := w.votes ++ [(me, t, to)] }
    | .send to msg => { w with inflight := w.inflight ++ [(me, to, msg)] }
    | .reply idx rid r =>
        { w with replies := w.replies ++ [(rid, r)],
                 answered := w.answered ++ [(idx, rid, r)] }
    | .notLeader rid _ => { w with refused := w.refused ++ [rid] }) w

/-- Deliver an event to node `i`. -/
def World.fire (w : World) (i : Nat) (ev : Event) : World :=
  if h : i < w.nodes.size then
    let s := w.nodes[i]
    let (s', acts) := Protocol.step s ev
    -- everything this step applied, for the durable history
    let fresh := (List.range (s'.lastApplied - s.lastApplied)).filterMap (fun d =>
      (LogStore.get s'.log (s.lastApplied + 1 + d)).map (fun e => (s.lastApplied + 1 + d, e)))
    let w := { w with nodes := w.nodes.set i s' h, applied := w.applied ++ fresh }
    w.absorb i acts
  else w

/--
Crash and restart node `i`: volatile state is lost, the durable trio survives.

Messages already in flight are unaffected — the network model already allows
them to be dropped or delivered late, so a crash needs no special treatment
there.
-/
def World.crash (w : World) (i : Nat) : World :=
  if h : i < w.nodes.size then
    { w with nodes := w.nodes.set i (Protocol.restart w.nodes[i]) h }
  else w

/--
Node `i` compacts its log: everything its state machine has already absorbed is
discarded and replaced by the snapshot.

Nothing observable changes, which is exactly what the safety checks should
confirm — they are phrased over histories, so they see every entry that was ever
applied whether or not the node still holds it.
-/
def World.compactNode (w : World) (i : Nat) : World :=
  if h : i < w.nodes.size then
    { w with nodes := w.nodes.set i (Protocol.compactTo w.nodes[i]) h }
  else w

/--
Restart node `i` with `f` applied to the recovered state.

Used to build **deliberately wrong** restarts that forget part of the durable
trio, so the tests can show which of the three durability obligations is
actually load-bearing.
-/
def World.crashWith (w : World) (i : Nat) (f : SNode → SNode) : World :=
  if h : i < w.nodes.size then
    { w with nodes := w.nodes.set i (f (Protocol.restart w.nodes[i])) h }
  else w

/-- Forgets everything — what today's server does, since it has no persistence. -/
def World.crashLosingAll (w : World) (i : Nat) : World :=
  w.crashWith i (fun s => Protocol.initState s.cfg)

/-- Keeps the term and the log, forgets the vote. -/
def World.crashForgetVote (w : World) (i : Nat) : World :=
  w.crashWith i (fun s => { s with votedFor := none })

/-- Keeps the vote and the log, forgets the term. -/
def World.crashForgetTerm (w : World) (i : Nat) : World :=
  w.crashWith i (fun s => { s with currentTerm := 0 })

/-- Keeps the term and the vote, forgets the log. -/
def World.crashForgetLog (w : World) (i : Nat) : World :=
  w.crashWith i (fun s => { s with log := LogStore.empty })

/--
**A node that sent before it persisted, and then crashed.**

The step's messages escape onto the network, but the node comes back at the
durable state it had *before* the step. This models a shim that executes actions
without first committing the durable trio, and it is the one failure mode the
crash rule above cannot express: the network model already permits losing
messages, but nothing permits losing state that a sent message depended on.

Used only to show that the write-before-send obligation on the I/O shim is real.
-/
def World.fireThenLose (w : World) (i : Nat) (ev : Event) : World :=
  if h : i < w.nodes.size then
    let pre := w.nodes[i]
    let w := w.fire i ev
    if h' : i < w.nodes.size then
      { w with nodes := w.nodes.set i (Protocol.restart pre) h' }
    else w
  else w

/-- Deliver the oldest in-flight message, if any. -/
def World.deliverOne (w : World) : World :=
  match w.inflight with
  | [] => w
  | (src, dst, msg) :: rest =>
      { w with inflight := rest }.fire dst (.recv src msg)

/-- Deliver messages until the network is quiet, bounded by `fuel`. -/
def World.settle : Nat → World → World
  | 0, w => w
  | fuel + 1, w => if w.inflight.isEmpty then w else World.settle fuel w.deliverOne

/-- The id of the current leader, if exactly one node believes it leads. -/
def World.leader (w : World) : Option Nat :=
  (List.range w.nodes.size).find? (fun i =>
    if h : i < w.nodes.size then w.nodes[i].role == .leader else false)

/-- Committed index at node `i`. -/
def World.commitAt (w : World) (i : Nat) : Nat :=
  if h : i < w.nodes.size then w.nodes[i].commitIndex else 0

/-- Value bound to `k` in node `i`'s applied state machine. -/
def World.readAt (w : World) (i : Nat) (k : String) : Option String :=
  if h : i < w.nodes.size then KVStore.find w.nodes[i].kv k else none

end RaftKV.Sim
