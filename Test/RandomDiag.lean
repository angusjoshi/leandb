import RaftKV.Runtime.Random
open RaftKV RaftKV.Sim

def maxCommit (w : World) : Nat :=
  (List.range w.nodes.size).foldl (fun a i => max a (w.commitAt i)) 0

def maxTerm (w : World) : Nat :=
  (List.range w.nodes.size).foldl (fun a i => max a (termOf w i)) 0

def anyLeader (w : World) : Bool :=
  (List.range w.nodes.size).any (fun i => roleAt w i == Role.leader)

/-- Aggregate over seeds: how many runs elected a leader, and the totals reached. -/
def diag (n steps count : Nat) : Nat × Nat × Nat :=
  (List.range count).foldl (fun (led, cm, tm) s =>
    let w := run n steps (World.init n) (s * 7919 + 1) 1
    ((if anyLeader w then led + 1 else led), cm + maxCommit w, max tm (maxTerm w))) (0, 0, 0)

#eval diag 3 400 100   -- (runs ending with a leader, total commits, max term)
#eval diag 5 800 100
