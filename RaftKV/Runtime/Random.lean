import RaftKV.Runtime.Sim

/-!
# Randomised schedule testing

Randomly generated schedules with message loss, reordering, duplication,
concurrent elections **and node crashes**, checked against the safety
properties.

Crashes are the reason this file still earns its keep. The proved theorems cover
a model with no crash rule, so they say nothing about a bouncing node; the
checks below are the cheap way to find out whether the durable-state design is
right *before* re-doing the proofs under a crash rule.

The checks are phrased over histories — every entry ever applied, every vote
ever granted, every reply ever sent — rather than over the final states, because
a restart zeroes `lastApplied` and a final-state check would simply stop seeing
anything that happened before a crash.

This is not a substitute for a proof and is not part of the trusted path.
-/

namespace RaftKV.Sim

open RaftKV Protocol

/-- A tiny deterministic PRNG, so every run is reproducible from its seed. -/
def next (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/--
One scheduling decision.

`crash` is how a node comes back after a bounce, so the same schedule can be
replayed against a correct durable restart and against one that forgets its
durable state.
-/
def tick (crash : World → Nat → World) (n : Nat) (rid : Nat) (w : World) (seed : Nat) :
    World × Nat :=
  let s := next seed
  let choice := s % 100
  let node := (s / 100) % n
  if choice < 72 then
    -- deliver the oldest in-flight message
    (w.deliverOne, s)
  else if choice < 77 then
    -- drop a message
    (match w.inflight with
     | [] => w
     | _ :: rest => { w with inflight := rest }, s)
  else if choice < 82 then
    -- duplicate a message
    (match w.inflight with
     | [] => w
     | p :: rest => { w with inflight := p :: p :: rest }, s)
  else if choice < 86 then
    (w.fire node .electionTimeout, s)
  else if choice < 92 then
    (w.fire node .heartbeatTimeout, s)
  else if choice < 96 then
    -- a mixed workload: reads and deletes as well as writes, so that a reply
    -- actually depends on the state and `repliesMatchSpec` has something to say
    let key := s!"k{rid % 3}"
    let cmd : Command :=
      match rid % 4 with
      | 0 => .put key s!"v{rid}"
      | 1 => .put key s!"v{rid}"
      | 2 => .get key
      | _ => .del key
    (w.fire node (.clientReq rid cmd), s)
  else if choice < 98 then
    -- compact a node's log, throwing away what its snapshot now covers
    (w.compactNode node, s)
  else
    -- crash and restart a node
    (crash w node, s)

/--
A schedule in which a node occasionally sends before it persists, then crashes.

Every scheduling decision is the same as `tick`'s, except that a small fraction
of the node-local events lose their durable write while their messages escape.
-/
def tickUnsafeShim (n : Nat) (rid : Nat) (w : World) (seed : Nat) : World × Nat :=
  let s := next seed
  let choice := s % 100
  let node := (s / 100) % n
  if choice < 72 then
    (match w.inflight with
     | [] => w
     | (src, dst, msg) :: rest =>
         if (s / 7) % 20 == 0 then
           { w with inflight := rest }.fireThenLose dst (.recv src msg)
         else { w with inflight := rest }.fire dst (.recv src msg), s)
  else if choice < 77 then
    (match w.inflight with
     | [] => w
     | _ :: rest => { w with inflight := rest }, s)
  else if choice < 82 then
    (match w.inflight with
     | [] => w
     | p :: rest => { w with inflight := p :: p :: rest }, s)
  else if choice < 86 then
    (w.fire node .electionTimeout, s)
  else if choice < 92 then
    (w.fire node .heartbeatTimeout, s)
  else if choice < 98 then
    (w.fire node (.clientReq rid (.put s!"k{rid % 3}" s!"v{rid}")), s)
  else
    (w.crash node, s)

def runUnsafeShim (n : Nat) : Nat → World → Nat → Nat → World
  | 0, w, _, _ => w
  | fuel + 1, w, seed, rid =>
      let (w', seed') := tickUnsafeShim n rid w seed
      runUnsafeShim n fuel w' seed' (rid + 1)

/-- Run `steps` scheduling decisions from `seed`. -/
def run (crash : World → Nat → World) (n : Nat) : Nat → World → Nat → Nat → World
  | 0, w, _, _ => w
  | fuel + 1, w, seed, rid =>
      let (w', seed') := tick crash n rid w seed
      run crash n fuel w' seed' (rid + 1)

/-! ## Property checks -/

/-- How much of the cluster's log has been compacted away, for diagnostics. -/
def compacted (w : World) : Nat :=
  (List.range w.nodes.size).foldl
    (fun acc i => acc + (if h : i < w.nodes.size then w.nodes[i].snapIndex else 0)) 0

/-- Indices worth checking. -/
def idxs (w : World) : List Nat :=
  List.range (1 + (List.range w.nodes.size).foldl
    (fun acc i => max acc (if h : i < w.nodes.size then LogStore.lastIndex w.nodes[i].log else 0)) 0)

def logAt (w : World) (i k : Nat) : Option Entry :=
  if h : i < w.nodes.size then LogStore.get w.nodes[i].log k else none

/-- The lowest index node `i` still holds. Above `1` once it has compacted. -/
def firstAt (w : World) (i : Nat) : Nat :=
  if h : i < w.nodes.size then LogStore.firstIndex w.nodes[i].log else 1

/-- Role of node `i`. -/
def roleAt (w : World) (i : Nat) : Role :=
  if h : i < w.nodes.size then w.nodes[i].role else .follower

/-- Current term of node `i`. -/
def termOf (w : World) (i : Nat) : Nat :=
  if h : i < w.nodes.size then w.nodes[i].currentTerm else 0

/-- Applied index of node `i`. -/
def appliedOf (w : World) (i : Nat) : Nat :=
  if h : i < w.nodes.size then w.nodes[i].lastApplied else 0

/-- **Election Safety**: at most one leader per term. -/
def electionSafe (w : World) : Bool :=
  (List.range w.nodes.size).all fun i =>
    (List.range w.nodes.size).all fun j =>
      !(roleAt w i == Role.leader && roleAt w j == Role.leader &&
        termOf w i == termOf w j) || i == j

/-- **Log Matching, part one**: same index and term implies the same entry. -/
def entriesAgree (w : World) : Bool :=
  (idxs w).all fun k =>
    (List.range w.nodes.size).all fun i =>
      (List.range w.nodes.size).all fun j =>
        match logAt w i k, logAt w j k with
        | some a, some b => !(a.term == b.term) || a == b
        | _, _ => true

/--
**Log Matching, part two**: agreement at an index implies agreement below —
at every index both nodes still hold.

The window guard is compaction's doing, and is exactly the one the theorem
carries: a node that has discarded a prefix no longer has the low entries to
compare, and that is not a disagreement.
-/
def prefixesAgree (w : World) : Bool :=
  (idxs w).all fun k =>
    (List.range w.nodes.size).all fun i =>
      (List.range w.nodes.size).all fun j =>
        match logAt w i k, logAt w j k with
        | some a, some b =>
            !(a == b) || (List.range (k + 1)).all fun m =>
              !(firstAt w i ≤ m && firstAt w j ≤ m) || logAt w i m == logAt w j m
        | _, _ => true

/-- **State Machine Safety**: applied entries never disagree. -/
def appliedAgree (w : World) : Bool :=
  (idxs w).all fun k =>
    (List.range w.nodes.size).all fun i =>
      (List.range w.nodes.size).all fun j =>
        if k ≤ appliedOf w i && k ≤ appliedOf w j then
          match logAt w i k, logAt w j k with
          | some a, some b => a == b
          | _, _ => true
        else true

/-! ### Checks over histories, which survive a restart -/

/--
**State Machine Safety, durably.** No index was *ever* applied with two
different entries — by any node, at any time, across any number of crashes.
-/
def appliedHistoryAgree (w : World) : Bool :=
  w.applied.all fun p => w.applied.all fun q => !(p.1 == q.1) || p.2 == q.2

/--
**Vote uniqueness.** No node ever granted two different candidates a vote in one
term. This is the property persistence exists to protect: a node that forgets
`votedFor` across a restart breaks it immediately.
-/
def voteUnique (w : World) : Bool :=
  w.votes.all fun p => w.votes.all fun q =>
    !(p.1 == q.1 && p.2.1 == q.2.1) || p.2.2 == q.2.2

/-- The entry the cluster settled on at index `k`, as witnessed by an application. -/
def canonEntry (w : World) (k : Nat) : Option Entry :=
  (w.applied.find? (fun p => p.1 == k)).map (fun p => p.2)

/-- The sequential specification's reply for the command at index `idx`. -/
def specReplyAt (w : World) (idx : Nat) : Option Reply :=
  match canonEntry w idx with
  | none => none
  | some e =>
      let m := (List.range (idx - 1)).foldl (fun m d =>
        match canonEntry w (d + 1) with
        | some e' => (Spec.applyCmd m e'.cmd).1
        | none => m) Spec.KVModel.empty
      some (Spec.applyCmd m e.cmd).2

/--
**Linearizability, clause one.** Every reply the cluster ever sent is what the
sequential specification returns for the command at that reply's log index, run
on the commands below it.
-/
def repliesMatchSpec (w : World) : Bool :=
  w.answered.all fun p =>
    match specReplyAt w p.1 with
    | some r => r == p.2.2
    | none => false

/-- All the checks. -/
def allSafe (w : World) : Bool :=
  electionSafe w && entriesAgree w && prefixesAgree w && appliedAgree w
    && appliedHistoryAgree w && voteUnique w && repliesMatchSpec w

/-- Run one seeded schedule with durable restarts, and report whether it stayed safe. -/
def check (n steps seed : Nat) : Bool :=
  allSafe (run World.crash n steps (World.init n) seed 1)

/-- The same schedule, but restarts forget the durable state — as today's server does. -/
def checkNoDurability (n steps seed : Nat) : Bool :=
  allSafe (run World.crashLosingAll n steps (World.init n) seed 1)

/-- Durable state, but a shim that sometimes sends before it persists. -/
def checkUnsafeShim (n steps seed : Nat) : Bool :=
  allSafe (runUnsafeShim n steps (World.init n) seed 1)

end RaftKV.Sim
