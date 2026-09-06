import RaftKV.Runtime.Sim

/-!
# Randomised schedule testing

The two safety properties this development does not prove — Leader Completeness
and State Machine Safety — are checked here empirically instead, over randomly
generated schedules with message loss, reordering, duplication, and concurrent
elections.

This is not a substitute for a proof and is not part of the trusted path. It is
a way of raising confidence in exactly the claims that remain unproved, using
the same pure `step` function the real server runs.
-/

namespace RaftKV.Sim

open RaftKV Protocol

/-- A tiny deterministic PRNG, so every run is reproducible from its seed. -/
def next (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- One scheduling decision. -/
def tick (n : Nat) (rid : Nat) (w : World) (seed : Nat) : World × Nat :=
  let s := next seed
  let choice := s % 100
  let node := (s / 100) % n
  if choice < 74 then
    -- deliver the oldest in-flight message
    (w.deliverOne, s)
  else if choice < 79 then
    -- drop a message
    (match w.inflight with
     | [] => w
     | _ :: rest => { w with inflight := rest }, s)
  else if choice < 84 then
    -- duplicate a message
    (match w.inflight with
     | [] => w
     | p :: rest => { w with inflight := p :: p :: rest }, s)
  else if choice < 88 then
    (w.fire node .electionTimeout, s)
  else if choice < 94 then
    (w.fire node .heartbeatTimeout, s)
  else
    (w.fire node (.clientReq rid (.put s!"k{rid % 3}" s!"v{rid}")), s)

/-- Run `steps` scheduling decisions from `seed`. -/
def run (n : Nat) : Nat → World → Nat → Nat → World
  | 0, w, _, _ => w
  | fuel + 1, w, seed, rid =>
      let (w', seed') := tick n rid w seed
      run n fuel w' seed' (rid + 1)

/-! ## Property checks -/

/-- Indices worth checking. -/
def idxs (w : World) : List Nat :=
  List.range (1 + (List.range w.nodes.size).foldl
    (fun acc i => max acc (if h : i < w.nodes.size then LogStore.lastIndex w.nodes[i].log else 0)) 0)

def logAt (w : World) (i k : Nat) : Option Entry :=
  if h : i < w.nodes.size then LogStore.get w.nodes[i].log k else none

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

/-- **Log Matching, part two**: agreement at an index implies agreement below. -/
def prefixesAgree (w : World) : Bool :=
  (idxs w).all fun k =>
    (List.range w.nodes.size).all fun i =>
      (List.range w.nodes.size).all fun j =>
        match logAt w i k, logAt w j k with
        | some a, some b =>
            !(a == b) || (List.range (k + 1)).all fun m => logAt w i m == logAt w j m
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

/-- All four checks. -/
def allSafe (w : World) : Bool :=
  electionSafe w && entriesAgree w && prefixesAgree w && appliedAgree w

/-- Run one seeded schedule and report whether every property held. -/
def check (n steps seed : Nat) : Bool :=
  allSafe (run n steps (World.init n) seed 1)

end RaftKV.Sim
