import RaftKV.Core.Types

/-!
# Protocol types: messages, events, actions, node state

The Raft node is a **pure function** `step : NodeState → Event → NodeState × List Action`.
Everything effectful is pushed to the edges: the runtime turns sockets and
timers into `Event`s, and executes the `Action`s that come back.

That is what makes the safety proof tractable. Asynchrony, reordering,
duplication and loss are not features of this code at all — they live only in
the `World` relation of `RaftKV.Protocol.Network`, which is proof-level.
-/

namespace RaftKV

/-- Static cluster configuration. Membership changes are out of scope. -/
structure Config where
  /-- This node's identifier. -/
  me : Nat
  /-- Identifiers of every cluster member, including `me`. -/
  members : List Nat
  deriving Repr, DecidableEq, Inhabited

namespace Config

/-- Number of nodes constituting a majority quorum. -/
def quorum (c : Config) : Nat := c.members.length / 2 + 1

/-- All members other than this node. -/
def peers (c : Config) : List Nat := c.members.filter (· != c.me)

/-- A peer is never the node itself. -/
theorem peers_ne {c : Config} {p : Nat} (h : p ∈ c.peers) : p ≠ c.me := by
  rw [peers, List.mem_filter] at h
  simpa using h.2

/--
Does this set of node ids constitute a majority?

`votes` is expected to be duplicate-free; every call site maintains that
(`votesGranted` is extended only after a `contains` check, and `advanceCommit`
builds its list by filtering `peers`). Carrying `Nodup` as an invariant rather
than deduplicating here keeps the quorum-intersection argument in
`RaftKV.Proof.Quorum` a straightforward counting proof.
-/
def isMajority (c : Config) (votes : List Nat) : Bool :=
  votes.length ≥ c.quorum

end Config

/-- The three Raft roles. -/
inductive Role where
  | follower
  | candidate
  | leader
  deriving Repr, DecidableEq, Inhabited

/-- Messages exchanged between replicas. -/
inductive Msg where
  /-- Candidate solicits a vote. -/
  | requestVote (term candidateId lastLogIndex lastLogTerm : Nat)
  /-- Reply to `requestVote`. -/
  | requestVoteResp (term : Nat) (granted : Bool)
  /-- Leader replicates entries (empty `entries` acts as a heartbeat). -/
  | appendEntries (term leaderId prevLogIndex prevLogTerm : Nat)
      (entries : List Entry) (leaderCommit : Nat)
  /-- Reply to `appendEntries`; `matchIndex` is the follower's new last replicated index. -/
  | appendEntriesResp (term : Nat) (success : Bool) (matchIndex : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Inputs to the node. Produced by the runtime, consumed by `step`. -/
inductive Event where
  /-- A message arrived from a peer. -/
  | recv (src : Nat) (msg : Msg)
  /-- A client submitted a command. -/
  | clientReq (reqId : Nat) (cmd : Command)
  /-- No leader contact for too long; start an election. -/
  | electionTimeout
  /-- Time for a leader to refresh its authority. -/
  | heartbeatTimeout
  deriving Repr, DecidableEq, Inhabited

/-- Outputs of the node. Produced by `step`, executed by the runtime. -/
inductive Action where
  /-- Send a message to a peer. Delivery is best-effort. -/
  | send (to : Nat) (msg : Msg)
  /-- Answer a client request that has now committed and applied. -/
  | reply (reqId : Nat) (r : Reply)
  /-- Refuse a client request, optionally naming the node believed to be leader. -/
  | notLeader (reqId : Nat) (leaderHint : Option Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A finite map from peer id to index, used for `nextIndex` and `matchIndex`. -/
def PeerMap := List (Nat × Nat)

namespace PeerMap

/-- The empty peer map. -/
def empty : PeerMap := []

/-- Look up a peer, falling back to `dflt`. -/
def get (m : PeerMap) (k : Nat) (dflt : Nat) : Nat := (List.lookup k m).getD dflt

/-- Bind a peer to a value, replacing any existing binding. -/
def set (m : PeerMap) (k v : Nat) : PeerMap := (k, v) :: m.filter (fun p => p.1 != k)

/-- Bind every peer in `ks` to `v`. -/
def setAll (ks : List Nat) (v : Nat) : PeerMap := ks.map (fun k => (k, v))

end PeerMap

/--
The complete state of one replica.

Parameterised over the log representation `σ` and the state-machine map `κ`, so
that neither this definition nor any proof about it mentions a concrete
implementation.
-/
structure NodeState (σ κ : Type) where
  /-- Static cluster configuration. -/
  cfg : Config
  /-- Latest term this node has seen. Never decreases. -/
  currentTerm : Nat
  /-- Candidate this node voted for in `currentTerm`, if any. -/
  votedFor : Option Nat
  /-- The replicated log. -/
  log : σ
  /-- Highest log index known to be committed. -/
  commitIndex : Nat
  /-- Highest log index applied to `kv`. -/
  lastApplied : Nat
  /-- Current role. -/
  role : Role
  /-- Votes received this term, when a candidate. -/
  votesGranted : List Nat
  /-- For each peer, the next log index to send. Leader only. -/
  nextIndex : PeerMap
  /-- For each peer, the highest index known replicated. Leader only. -/
  matchIndex : PeerMap
  /-- The replicated state machine. -/
  kv : κ
  /-- Client requests awaiting commit, as `(logIndex, reqId)`. Leader only. -/
  pending : List (Nat × Nat)
  /-- Last known leader, used to redirect clients. -/
  leaderHint : Option Nat

end RaftKV
