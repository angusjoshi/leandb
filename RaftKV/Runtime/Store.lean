import RaftKV.Storage.NodePersist
import RaftKV.Storage.KVHash
import RaftKV.Runtime.Posix

/-!
# The durable store, on a real filesystem

The `IO` shim for `RaftKV.Storage.Persist`. It performs exactly the sequence the
crash-safety theorem is about:

```
writeAt    write the image where the live root cannot see it
flushUser  hand it to the kernel
fsync      force it to the platter          -- load-bearing
setRoot    swap the root
flushUser  hand that to the kernel
fsync      force it to the platter          -- load-bearing
```

Both `fsync`s matter. `Format.flushOnly_not_crash_safe` exhibits a crash after
which a flush-only commit comes back holding *neither* the old value nor the new
one, so this is not a belt-and-braces call that could be dropped for speed.

Because Lean's `IO.FS` offers no `fsync` — its `flush` is `fflush`, which reaches
the kernel and stops there — the store is built on `RaftKV.Posix`, a small FFI
binding to `open`, `pread`, `pwrite`, `fsync` and `close`. Positional writes come
along with it, so the layout is the two regions plus a root record that
`Persist` describes rather than whole-file rewrites.

The root swap is a `rename` over the root file, which POSIX makes atomic:
after a crash the directory entry names the old root or the new one and never a
mixture. That is the model's single-word atomicity, obtained from the filesystem.
The directory is fsynced afterwards so the rename itself is durable.

**Not verified, and in the trusted base:**

* This file and `RaftKV.Posix`. They make no protocol decisions; they move bytes.
* `rename` atomicity, and that `fsync` on the containing directory makes a
  rename durable.
* That the device's own `fsync` reaches stable storage. On macOS the shim asks
  for `F_FULLFSYNC`, which bypasses the drive's write cache.
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

/-- Write a whole file and force it to the platter. -/
def writeDurable (path : System.FilePath) (bs : ByteArray) : IO Unit := do
  let fd ← Posix.open' path.toString
  try
    Posix.pwrite fd 0 bs
    Posix.fsync fd
  finally
    Posix.close fd

/--
Commit a node's durable state.

The six steps of `Format.commitOps`, in order, with both `fsync`s. The `rename`
is the root swap and therefore the commit point: before it a crash recovers the
previous state, after it the new one. Neither `fsync` may be dropped — see
`Format.flushOnly_not_crash_safe`.
-/
def commit (p : Paths) (dir : System.FilePath) (st : Persistent ArrayLog) : IO Unit := do
  let live := (← readRoot p).map Prod.fst |>.getD false
  let target := !live
  let img := (ByteCodec.enc st).toByteArray
  -- writeAt, flushUser, fsync: the image is durable before anything points at it
  writeDurable (if target then p.regionB else p.regionA) img
  -- setRoot, flushUser, fsync: the root record, then the atomic swap
  writeDurable p.rootTmp (encRoot target img.size)
  IO.FS.rename p.rootTmp p.root
  -- the rename itself is only durable once the directory is synced
  Posix.fsyncDir dir.toString

/-- Restore a node from disk, or start it fresh. -/
def load (p : Paths) (cfg : Config) : IO (NodeState ArrayLog HashKV) := do
  match ← recover p with
  | none => return Protocol.initState cfg
  | some st => return Protocol.recoverNode cfg st

end RaftKV.Store
