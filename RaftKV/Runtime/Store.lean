import RaftKV.Storage.NodePersist
import RaftKV.Storage.KVHash

/-!
# The durable store, on a real filesystem

The `IO` shim for `RaftKV.Storage.Persist`. It performs exactly the sequence the
crash-safety theorem is about:

```
write the image where the live root cannot see it   -- writeAt
flush                                               -- sync
swap the root, atomically                           -- setRoot
flush                                               -- sync
```

The two regions are two files, `a` and `b`, and the root is a third file holding
one byte for the live side and the image length. The root swap is a `rename`
over the root file, which POSIX makes atomic: after a crash the directory entry
names the old root or the new one, never a mixture. That is the single-word
atomicity the disk model assumes, obtained from the filesystem rather than from
the drive.

Because nothing reachable from the live root is ever overwritten — a commit
always writes the *other* region — a torn write can only damage space no reader
will look at, which is what `Format.commit_crash_safe` needs.

**Not verified, and in the trusted base:**

* This file. It makes no protocol decisions; it moves bytes.
* `rename` atomicity, and that a rename is ordered after the writes it publishes.
* **`fsync` is missing.** Lean's `IO.FS` exposes `flush`, which pushes to the
  operating system but not to the platter. A process crash is therefore fully
  covered — the kernel keeps the buffers — but a power cut is not. Closing that
  is one `fsync(2)` binding, and it is the only thing between this file and the
  durability the proof assumes.
-/

namespace RaftKV.Store

open RaftKV Protocol

/-- Where a node keeps its durable state. -/
structure Paths where
  /-- The `a` region. -/
  regionA : System.FilePath
  /-- The `b` region. -/
  regionB : System.FilePath
  /-- The root: live side and image length. -/
  root : System.FilePath
  /-- Scratch, renamed over `root` to publish a commit. -/
  rootTmp : System.FilePath

/-- The files for node `i` under `dir`. -/
def Paths.forNode (dir : System.FilePath) (i : Nat) : Paths :=
  { regionA := dir / s!"node{i}.a"
    regionB := dir / s!"node{i}.b"
    root := dir / s!"node{i}.root"
    rootTmp := dir / s!"node{i}.root.tmp" }

/-- The root record: which side is live, and how many bytes the image is. -/
def encRoot (side : Bool) (len : Nat) : ByteArray :=
  (ByteCodec.enc side ++ ByteCodec.enc len).toByteArray

/-- Read the root, or `none` if it is absent or unreadable. -/
def readRoot (p : Paths) : IO (Option (Bool × Nat)) := do
  if ← p.root.pathExists then
    let bs ← IO.FS.readBinFile p.root
    match (ByteCodec.dec bs.toList : Option (Bool × List UInt8)) with
    | none => return none
    | some (side, rest) =>
        match (ByteCodec.dec rest : Option (Nat × List UInt8)) with
        | none => return none
        | some (len, _) => return some (side, len)
  else
    return none

/-- Read back the durable state, or `none` on a fresh node. -/
def recover (p : Paths) : IO (Option (Persistent ArrayLog)) := do
  match ← readRoot p with
  | none => return none
  | some (side, len) =>
      let file := if side then p.regionB else p.regionA
      if ← file.pathExists then
        let bs ← IO.FS.readBinFile file
        -- the root says how long the image is; ignore anything past it
        let img := bs.toList.take len
        return (ByteCodec.dec img : Option (Persistent ArrayLog × List UInt8)).map Prod.fst
      else
        return none

/--
Commit a node's durable state.

The four steps of `Format.commitOps`, in order. The final `rename` is the commit
point: before it, a crash recovers the previous state; after it, the new one.
-/
def commit (p : Paths) (st : Persistent ArrayLog) : IO Unit := do
  let live := (← readRoot p).map Prod.fst |>.getD false
  let target := !live
  let img := (ByteCodec.enc st).toByteArray
  -- 1. write the image where the live root cannot see it, and 2. flush it
  IO.FS.writeBinFile (if target then p.regionB else p.regionA) img
  -- 3. publish the new root atomically, and 4. flush it
  IO.FS.writeBinFile p.rootTmp (encRoot target img.size)
  IO.FS.rename p.rootTmp p.root

/-- Restore a node from disk, or start it fresh. -/
def load (p : Paths) (cfg : Config) : IO (NodeState ArrayLog HashKV) := do
  match ← recover p with
  | none => return Protocol.initState cfg
  | some st => return Protocol.recoverNode cfg st

end RaftKV.Store
