import RaftKV

open RaftKV RaftKV.Runtime Std Std.Async

/-- `127.0.0.1:port` -/
def loopback (port : Nat) : Net.SocketAddress :=
  .v4 { addr := Net.IPv4Addr.ofParts 127 0 0 1, port := UInt16.ofNat port }

/-- Inter-node port for a replica. -/
def raftPort (base id : Nat) : Nat := base + id

/-- Client HTTP port for a replica. -/
def httpPort (base id : Nat) : Nat := base + 100 + id

def usage : String :=
  "usage: raftkv <nodeId> <clusterSize> [basePort=9000] [dataDir]\n\n\
   Ports: raft = base + id, http = base + 100 + id\n\
   API:   GET /status, GET|PUT|DELETE /kv/<key>\n\
   Data:  with a dataDir the durable trio is persisted and recovered on start;\n\
          without one the replica keeps everything in memory.\n"

def main (args : List String) : IO Unit := do
  match args with
  | [idS, nS] | [idS, nS, _] | [idS, nS, _, _] => do
    let some id := idS.toNat? | IO.eprintln usage
    let some n := nS.toNat? | IO.eprintln usage
    let base := (args[2]? >>= String.toNat?).getD 9000
    if n = 0 || id ≥ n then
      IO.eprintln s!"node id {id} out of range for cluster size {n}"
    else
      let cfg : Config := { me := id, members := List.range n }
      let peers := (List.range n).filter (· != id) |>.map (fun p => (p, loopback (raftPort base p)))
      let dataDir : Option System.FilePath :=
        (args[3]? : Option String).map (fun d => (⟨d⟩ : System.FilePath))
      let nd ← Node.create cfg peers dataDir
      Async.block (nd.run (loopback (raftPort base id)) (loopback (httpPort base id)))
  | _ => IO.eprintln usage
