import RaftKV.Runtime.Random
open RaftKV RaftKV.Sim

/-- Count schedules on which any safety property failed. -/
def sweep (n steps count : Nat) : Nat :=
  (List.range count).foldl (fun bad s => if check n steps (s * 7919 + 1) then bad else bad + 1) 0

#eval sweep 3 400 300   -- 3 nodes
#eval sweep 5 800 200   -- 5 nodes
#eval sweep 3 1200 60   -- long schedules
#eval sweep 4 600 150   -- even cluster size

/-- Sanity: a deliberately broken check must be caught, so the sweep is not vacuous. -/
def brokenCheck (n steps seed : Nat) : Bool :=
  let w := run n steps (World.init n) seed 1
  -- claim (falsely) that no node ever reaches commit index 1
  (List.range w.nodes.size).all (fun i => w.commitAt i == 0)

#eval (List.range 300).foldl
  (fun bad s => if brokenCheck 3 400 (s * 7919 + 1) then bad else bad + 1) 0
