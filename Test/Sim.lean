import RaftKV.Runtime.Sim
open RaftKV RaftKV.Sim

/-- Elect node 0 in a 3-node cluster, then run a few client commands. -/
def scenario : World := Id.run do
  let mut w := World.init 3
  w := (w.fire 0 .electionTimeout).settle 100
  w := (w.fire 0 (.clientReq 1 (.put "k" "v1"))).settle 100
  w := (w.fire 0 (.clientReq 2 (.get "k"))).settle 100
  w := (w.fire 0 (.clientReq 3 (.put "k" "v2"))).settle 100
  w := (w.fire 0 (.clientReq 4 (.get "k"))).settle 100
  w := (w.fire 1 (.clientReq 5 (.get "k"))).settle 100
  pure w

#eval scenario.leader
#eval scenario.replies
#eval scenario.refused
#eval (List.range 3).map (fun i => (i, scenario.commitAt i, scenario.readAt i "k"))
