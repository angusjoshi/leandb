import RaftKV.Runtime.Random
open RaftKV RaftKV.Sim

/-! ## Sweep 1 — durable restarts

Schedules with message loss, reordering, duplication, concurrent elections and
node crashes, where a restart keeps Raft's durable trio (`currentTerm`,
`votedFor`, the log) and rebuilds everything else. This is the design we intend
to prove.
-/

/-- Count schedules on which any safety property failed. -/
def sweep (n steps count : Nat) : Nat :=
  (List.range count).foldl (fun bad s => if check n steps (s * 7919 + 1) then bad else bad + 1) 0

#eval sweep 3 400 300   -- 3 nodes
#eval sweep 5 800 200   -- 5 nodes
#eval sweep 3 1200 60   -- long schedules
#eval sweep 4 600 150   -- even cluster size

/-! ## Sweep 1b — schedules that force snapshot transfer

The ordinary mix reaches the state `InstallSnapshot` exists for only by accident:
10 of 300 schedules above produce one. Here node 0's inbound traffic is dropped
30% of the time, so it falls far behind while the rest of the cluster keeps
committing and compacting — and a leader can no longer serve it from the log.

Observed: 83 of 200 schedules ship at least one snapshot, 199 in all, and **0
safety failures**.
-/

def sweepLagging (n steps count : Nat) : Nat :=
  (List.range count).foldl
    (fun bad s => if checkLagging n steps (s * 7919 + 1) then bad else bad + 1) 0

/-- How many schedules shipped a snapshot, and how many were shipped in all. -/
def snapStats (n steps count : Nat) : Nat × Nat :=
  (List.range count).foldl (fun (runs, total) s =>
    let w := runLagging n steps (World.init n) (s * 7919 + 1) 1
    let k := snapshotsSent w
    ((if k > 0 then runs + 1 else runs), total + k)) (0, 0)

#eval sweepLagging 3 600 200
#eval snapStats 3 600 200

/-! ## Sweep 2 — restarts that forget

The same schedules, but a restart forgets the durable state — which is exactly
what today's server does, since it has no persistence. This must **fail**: a
node that forgets `votedFor` can vote twice in a term. A zero here would mean
the crash tests have no teeth.
-/

def sweepNoDurability (n steps count : Nat) : Nat :=
  (List.range count).foldl
    (fun bad s => if checkNoDurability n steps (s * 7919 + 1) then bad else bad + 1) 0

#eval sweepNoDurability 3 400 300
#eval sweepNoDurability 5 800 200

/-! ## Experiment — which durability obligations are load-bearing

The same schedules, replayed against restarts that forget exactly one of Raft's
durable trio. Each column is the number of schedules (out of 300) on which that
check failed.

Expected shape, and what was observed:

| restart keeps        | applied-history | vote-uniqueness | replies-vs-spec |
|----------------------|-----------------|-----------------|-----------------|
| all three (`crash`)  | 0               | 0               | 0               |
| forgets `votedFor`   | 0               | 2               | 0               |
| forgets `currentTerm`| 0               | 50              | 0               |
| forgets the log      | 100             | 0               | 45              |
| forgets everything   | 84              | 48              | 32              |

Forgetting `currentTerm` breaks voting even though `votedFor` survived: a node
back at term 0 treats almost any incoming request as newer, steps down, and
`stepDown` clears the vote. That is why Raft persists the term *and* the vote,
not just the vote.

Forgetting `votedFor` alone fails on only 2 schedules in 300 — a reminder that
testing cannot substitute for the proof, since a 0.7% failure rate is exactly
the kind that survives a test suite and bites in production.
-/

def breakdown (crash : World → Nat → World) (n steps count : Nat) : Nat × Nat × Nat :=
  (List.range count).foldl (fun (ap, vu, rs) s =>
    let w := run crash n steps (World.init n) (s * 7919 + 1) 1
    ((if appliedHistoryAgree w then ap else ap + 1),
     (if voteUnique w then vu else vu + 1),
     (if repliesMatchSpec w then rs else rs + 1))) (0, 0, 0)

#eval breakdown World.crash           3 400 300   -- the design
#eval breakdown World.crashForgetVote 3 400 300
#eval breakdown World.crashForgetTerm 3 400 300
#eval breakdown World.crashForgetLog  3 400 300
#eval breakdown World.crashLosingAll  3 400 300

/-! ## Experiment — the shim must persist before it sends

Durable state, but a shim that sometimes lets a step's messages escape before
its durable write lands. The crash rule cannot express this: the network model
already allows losing messages, but nothing allows losing state that an escaped
message depended on. So it is an obligation on the I/O shim, and this is the
evidence that it is a real one rather than a theoretical one.

Observed: 9 vote-uniqueness failures in 300 on three nodes, and 66 in 200 on
five.
-/

def breakdownShim (n steps count : Nat) : Nat × Nat × Nat :=
  (List.range count).foldl (fun (ap, vu, rs) s =>
    let w := runUnsafeShim n steps (World.init n) (s * 7919 + 1) 1
    ((if appliedHistoryAgree w then ap else ap + 1),
     (if voteUnique w then vu else vu + 1),
     (if repliesMatchSpec w then rs else rs + 1))) (0, 0, 0)

#eval breakdownShim 3 400 300
#eval breakdownShim 5 800 200

/-! ## Sanity: the checks catch a deliberately false property -/

/-- Sanity: a deliberately broken check must be caught, so the sweep is not vacuous. -/
def brokenCheck (n steps seed : Nat) : Bool :=
  let w := run World.crash n steps (World.init n) seed 1
  -- claim (falsely) that no node ever reaches commit index 1
  (List.range w.nodes.size).all (fun i => w.commitAt i == 0)

#eval (List.range 300).foldl
  (fun bad s => if brokenCheck 3 400 (s * 7919 + 1) then bad else bad + 1) 0
