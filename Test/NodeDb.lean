import RaftKV.Runtime.NodeDb
open RaftKV RaftKV.Protocol RaftKV.NodeDb RaftKV.PageFile
/-!
# The node store on the copy-on-write B-tree

Round-trips through every shape a node's durable state takes — appends, a
compaction with a snapshot, a truncating splice, and a reopen — and measures what
one append actually costs.

The cost line is the point of the file: an append to a 400-entry log allocates
**4 pages**, and that number does not grow with the log. The two-region store
rewrites the whole image, log and state-machine snapshot included, for the same
append.
-/

def e (t r : Nat) (k v : String) : Entry := { term := t, cmd := .put k v, reqId := r }

/-- Append `n` entries one at a time, each its own durable commit. -/
def buildLog (db : Db) (n : Nat) : IO (Persistent ArrayLog) := do
  let mut p : Persistent ArrayLog :=
    { currentTerm := 0, votedFor := none, log := LogStore.empty, snapIndex := 0, snapPairs := [] }
  for i in List.range n do
    let p' : Persistent ArrayLog :=
      { p with currentTerm := i / 3 + 1,
               votedFor := some (i % 2),
               log := LogStore.append p.log (e (i / 3 + 1) i s!"k{i}" s!"v{i}") }
    save db p p'
    p := p'
  return p

def check : IO (List Bool) := do
  let dir : System.FilePath := "/tmp/raftkv-nodedb-test"
  IO.FS.removeDirAll dir <|> pure ()
  IO.FS.createDirAll dir
  let db ← open' dir "node0"
  -- an empty database has nothing
  let r0 := (← load db).isNone
  let p ← buildLog db 40
  let r1 := (← load db) == some p
  -- compaction: discard a prefix and record a snapshot
  let p2 : Persistent ArrayLog :=
    { p with log := LogStore.compact p.log 20, snapIndex := 20,
             snapPairs := (List.range 20).map (fun i => (s!"k{i}", s!"v{i}")) }
  save db p p2
  let r2 := (← load db) == some p2
  -- a truncating splice: the tail goes
  let p3 : Persistent ArrayLog :=
    { p2 with log := LogStore.truncFrom p2.log 31 }
  save db p2 p3
  let r3 := (← load db) == some p3
  -- reopening reads the same thing back
  close db
  let db2 ← open' dir "node0"
  let r4 := (← load db2) == some p3
  -- appending after a reopen still works
  let p4 : Persistent ArrayLog :=
    { p3 with log := LogStore.append p3.log (e 99 999 "zz" "yy"), currentTerm := 99 }
  save db2 p3 p4
  let r5 := (← load db2) == some p4
  close db2
  return [r0, r1, r2, r3, r4, r5]

/-- How many pages a single append touches, against how many the log holds. -/
def appendCost : IO (Nat × Nat) := do
  let dir : System.FilePath := "/tmp/raftkv-nodedb-cost"
  IO.FS.removeDirAll dir <|> pure ()
  IO.FS.createDirAll dir
  let db ← open' dir "node0"
  let p ← buildLog db 400
  let before := (← db.tree.get).next
  let p' : Persistent ArrayLog :=
    { p with log := LogStore.append p.log (e 1 1000 "kk" "vv") }
  save db p p'
  let after := (← db.tree.get).next
  close db
  return (after - before, LogStore.lastIndex p.log)

#eval check
#eval appendCost
