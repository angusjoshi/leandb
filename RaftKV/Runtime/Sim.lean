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
  deriving Inhabited

/-- Build an `n`-node cluster with empty logs. -/
def World.init (n : Nat) : World :=
  { nodes := (List.range n).toArray.map (fun i =>
      Protocol.initState { me := i, members := List.range n })
    inflight := [], replies := [], refused := [] }

/-- Route one node's emitted actions into the world. -/
def World.absorb (w : World) (me : Nat) (acts : List Action) : World :=
  acts.foldl (fun w a =>
    match a with
    | .send to msg => { w with inflight := w.inflight ++ [(me, to, msg)] }
    | .reply _ rid r => { w with replies := w.replies ++ [(rid, r)] }
    | .notLeader rid _ => { w with refused := w.refused ++ [rid] }) w

/-- Deliver an event to node `i`. -/
def World.fire (w : World) (i : Nat) (ev : Event) : World :=
  if h : i < w.nodes.size then
    let (s', acts) := Protocol.step w.nodes[i] ev
    let w := { w with nodes := w.nodes.set i s' h }
    w.absorb i acts
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
