import RaftKV
open RaftKV RaftKV.Protocol RaftKV.Store

/-!
Round-trip the durable store through a real filesystem, including the
alternating regions that make a commit copy-on-write.
-/

def sample (t : Nat) (v : Option Nat) (n : Nat) : Persistent ArrayLog :=
  { currentTerm := t, votedFor := v
    log := ⟨(List.range n).toArray.map (fun i =>
      { term := i + 1, cmd := .put s!"k{i}" s!"v{i}", reqId := i })⟩ }

def check : IO (List Bool) := do
  let dir : System.FilePath := "/tmp/raftkv-store-test"
  IO.FS.createDirAll dir
  let p := Paths.forNode dir 0
  -- a fresh node has nothing
  for f in [p.regionA, p.regionB, p.root, p.rootTmp] do
    if ← f.pathExists then IO.FS.removeFile f
  let fresh := (← recover p).isNone
  -- commit, recover, commit again (flipping regions), recover again
  let s1 := sample 3 (some 2) 4
  commit p dir s1
  let r1 ← recover p
  let live1 := (← readRoot p).map Prod.fst
  let s2 := sample 9 none 7
  commit p dir s2
  let r2 ← recover p
  let live2 := (← readRoot p).map Prod.fst
  let s3 := sample 9 (some 0) 0
  commit p dir s3
  let r3 ← recover p
  let live3 := (← readRoot p).map Prod.fst
  -- commits alternate regions, so the live image is never the one being written
  return [fresh, r1 == some s1, r2 == some s2, r3 == some s3,
    live1 == some true, live2 == some false, live3 == some true]

#eval check
