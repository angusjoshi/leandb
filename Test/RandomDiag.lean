import RaftKV.Runtime.Random
open RaftKV RaftKV.Sim

def maxCommit (w : World) : Nat :=
  (List.range w.nodes.size).foldl (fun a i => max a (w.commitAt i)) 0

def maxTerm (w : World) : Nat :=
  (List.range w.nodes.size).foldl (fun a i => max a (termOf w i)) 0

def anyLeader (w : World) : Bool :=
  (List.range w.nodes.size).any (fun i => roleAt w i == Role.leader)

/--
Aggregate over seeds: how many runs elected a leader, how many entries were
ever applied, how many replies were ever sent, and the highest term reached.

With crashes in the mix these numbers are what tell us the sweep is not
vacuous — a schedule that never elects anyone or never applies anything checks
nothing.
-/
def diag (n steps count : Nat) : Nat × Nat × Nat × Nat :=
  (List.range count).foldl (fun (led, ap, rep, tm) s =>
    let w := run World.crash n steps (World.init n) (s * 7919 + 1) 1
    ((if anyLeader w then led + 1 else led), ap + w.applied.length,
     rep + w.answered.length, max tm (maxTerm w))) (0, 0, 0, 0)

#eval diag 3 400 100   -- (runs with a leader, entries applied, replies sent, max term)
#eval diag 5 800 100
