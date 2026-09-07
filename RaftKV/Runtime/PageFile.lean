import RaftKV.Storage.BTree
import RaftKV.Runtime.Posix
import Std.Data.HashMap

/-!
# The copy-on-write B-tree, on a real file

`RaftKV.BTree` is pure: it maps a key and a page reader to the new root cell and
the list of pages to write. This file is the `IO` shim that gives it a file, and
it performs exactly the sequence `RaftKV.Storage.Persist` proves crash-safe:

```
  pwrite every new page      -- all at or above the old high-water mark
  fsync                      -- load-bearing: the pages are on the platter …
  write the new root cell    -- … before anything points at them
  rename over the root       -- the commit point, atomic by POSIX
  fsync the directory        -- and durable
```

The first `fsync` is what makes the second step safe to take, and the rename is
what makes it a commit rather than a smear. Crash before the rename and the old
root cell is still there, still naming pages nothing in the commit touched;
crash after it and every page it names was fsynced before the rename was issued.

## Page cache

The pure operations need a `Pages` function, but reads are `IO`. Rather than
hold the whole file in memory, the shim walks the search path in `IO` first and
caches just those nodes. That is exactly the set an insert or a delete can
touch — copy-on-write rewrites the root-to-leaf path and nothing else — so the
pure operation never asks for a page the cache lacks. Scans are the exception
and load what they read.

**Not verified, and in the trusted base**, on the same footing as
`RaftKV.Runtime.Store`: this file, `RaftKV.Posix`, `rename` atomicity, and that
the device's `fsync` reaches stable storage.
-/

namespace RaftKV.PageFile

open RaftKV RaftKV.BTree

/-- An open database: the page file, and the root cell that names its tree. -/
structure Db where
  /-- Descriptor for the page file. -/
  fd : Posix.Fd
  /-- Directory holding it, for fsyncing renames. -/
  dir : System.FilePath
  /-- The root cell. -/
  rootPath : System.FilePath
  /-- Scratch, renamed over the root cell to publish a commit. -/
  rootTmp : System.FilePath
  /-- The live root cell, mirrored in memory. -/
  tree : IO.Ref Tree

/-- Read page `p`, or `none` if it is absent, short, or fails its checksum. -/
def readPage (db : Db) (p : Nat) : IO (Option Node) := do
  let bs ← Posix.pread db.fd (USize.ofNat (p * pageSize)) (USize.ofNat pageSize)
  return decodePage p bs

/-- Write page `p`. No flushing: the caller decides where the fsyncs go. -/
def writePage (db : Db) (p : Nat) (n : Node) : IO Unit := do
  match encodePage p n with
  | none => throw (IO.userError s!"page {p} does not fit")
  | some bs => Posix.pwrite db.fd (USize.ofNat (p * pageSize)) bs

/-- The root cell's bytes. -/
def encRoot (t : Tree) : ByteArray :=
  (ByteCodec.enc t.root ++ ByteCodec.enc t.next).toByteArray

/-- Read the root cell, or the empty tree if there is not one yet. -/
def readRootCell (path : System.FilePath) : IO Tree := do
  if ← path.pathExists then
    let bs ← IO.FS.readBinFile path
    match (ByteCodec.dec bs.toList : Option (Option Nat × List UInt8)) with
    | none => return Tree.empty
    | some (r, rest) =>
        match (ByteCodec.dec rest : Option (Nat × List UInt8)) with
        | none => return Tree.empty
        | some (n, _) => return { root := r, next := n }
  else
    return Tree.empty

/-- Open (or create) the database rooted at `dir/name`. -/
def open' (dir : System.FilePath) (name : String) : IO Db := do
  IO.FS.createDirAll dir
  let fd ← Posix.open' (dir / s!"{name}.pages").toString
  let rootPath := dir / s!"{name}.root"
  let t ← readRootCell rootPath
  let ref ← IO.mkRef t
  return { fd, dir, rootPath, rootTmp := dir / s!"{name}.root.tmp", tree := ref }

/-- Close the database. Committed data is already durable. -/
def close (db : Db) : IO Unit := Posix.close db.fd

/--
Publish a commit: the pages, then a barrier, then the root.

The order is the whole point and must not be rearranged for speed.
-/
def commit (db : Db) (t' : Tree) (ws : List (Nat × Node)) : IO Unit := do
  for (p, n) in ws do
    writePage db p n
  -- barrier: every new page is on the platter before the root can name one
  Posix.fsync db.fd
  let fd ← Posix.open' db.rootTmp.toString
  try
    Posix.pwrite fd 0 (encRoot t')
    Posix.fsync fd
  finally
    Posix.close fd
  -- the commit point
  IO.FS.rename db.rootTmp db.rootPath
  Posix.fsyncDir db.dir.toString
  db.tree.set t'

/-- Cache the nodes on the search path for `k`, which is all an update can touch. -/
partial def cachePath (db : Db) (t : Tree) (k : Nat)
    (c : Std.HashMap Nat Node) (p : Nat) : IO (Std.HashMap Nat Node) := do
  if !(p < t.next) then return c
  match ← readPage db p with
  | none => return c
  | some n =>
      let c := c.insert p n
      match n with
      | .leaf _ => return c
      | .branch keys children =>
          match children[childIndex keys k]? with
          | none => return c
          | some ch => cachePath db t k c ch

/-- Cache every page the tree reaches. Used for scans. -/
partial def cacheAll (db : Db) (t : Tree)
    (c : Std.HashMap Nat Node) (p : Nat) : IO (Std.HashMap Nat Node) := do
  if !(p < t.next) then return c
  match ← readPage db p with
  | none => return c
  | some n =>
      let c := c.insert p n
      match n with
      | .leaf _ => return c
      | .branch _ children => children.foldlM (fun c ch => cacheAll db t c ch) c

/-- A `Pages` view of a cache. -/
def ofCache (c : Std.HashMap Nat Node) : Pages := fun p => c[p]?

/-- Cache the search path for `k` from the current root. -/
def pathPages (db : Db) (t : Tree) (k : Nat) : IO Pages := do
  match t.root with
  | none => return fun _ => none
  | some r => return ofCache (← cachePath db t k ∅ r)

/-- The value bound to `k`. -/
def Db.get (db : Db) (k : Nat) : IO (Option ByteArray) := do
  let t ← db.tree.get
  return t.lookup (← pathPages db t k) k

/-- Bind `k ↦ v`, durably. -/
def Db.put (db : Db) (k : Nat) (v : ByteArray) : IO Unit := do
  let t ← db.tree.get
  match t.insert (← pathPages db t k) k v with
  | none => throw (IO.userError s!"value for key {k} does not fit in a page")
  | some (t', ws) => commit db t' ws

/-- Remove `k`, durably. -/
def Db.del (db : Db) (k : Nat) : IO Unit := do
  let t ← db.tree.get
  match t.erase (← pathPages db t k) k with
  | none => throw (IO.userError s!"delete of key {k} could not find its path")
  | some (t', ws) => commit db t' ws

/-! ## Batched updates

A single commit may have to change several keys at once — a node's durable state
is a handful of them, and they must land together or not at all. The pure
operations already compose: each returns the new root cell and the pages it
allocated, and the allocator only ever hands out pages at or above the previous
high-water mark, so the pages one operation writes are exactly the ones the next
should read. Threading them through a pending map is all it takes, and the whole
batch is published by the same six-step commit as a single key.
-/

/-- Read page `p`, preferring one this batch has already written. -/
def readPageWith (db : Db) (pend : Std.HashMap Nat Node) (p : Nat) : IO (Option Node) := do
  match pend[p]? with
  | some n => return some n
  | none => readPage db p

/-- Cache the search path for `k`, reading through the batch's pending pages. -/
partial def cachePathWith (db : Db) (t : Tree) (pend : Std.HashMap Nat Node) (k : Nat)
    (c : Std.HashMap Nat Node) (p : Nat) : IO (Std.HashMap Nat Node) := do
  if !(p < t.next) then return c
  match ← readPageWith db pend p with
  | none => return c
  | some n =>
      let c := c.insert p n
      match n with
      | .leaf _ => return c
      | .branch keys children =>
          match children[childIndex keys k]? with
          | none => return c
          | some ch => cachePathWith db t pend k c ch

/-- One update in a batch: a binding to write, or a key to remove. -/
abbrev Op := Nat × Option ByteArray

/--
Apply a whole batch in one commit.

Nothing reaches the root cell until every operation has been applied, so a crash
part-way through leaves the tree exactly as it was — which is what makes this
usable for a node's durable state, where the term, the vote and the log have to
move together.
-/
def Db.update (db : Db) (ops : List Op) : IO Unit := do
  if ops.isEmpty then return
  let t0 ← db.tree.get
  let mut t := t0
  let mut pend : Std.HashMap Nat Node := ∅
  for (k, ov) in ops do
    let pages : Pages ← do
      match t.root with
      | none => pure (fun _ => none)
      | some r => pure (ofCache (← cachePathWith db t pend k ∅ r))
    let combined : Pages := fun p =>
      match pend[p]? with
      | some n => some n
      | none => pages p
    match ov with
    | some v =>
        match t.insert combined k v with
        | none => throw (IO.userError s!"value for key {k} does not fit in a page")
        | some (t', ws) =>
            t := t'
            pend := ws.foldl (fun m pn => m.insert pn.1 pn.2) pend
    | none =>
        match t.erase combined k with
        | none => throw (IO.userError s!"delete of key {k} could not find its path")
        | some (t', ws) =>
            t := t'
            pend := ws.foldl (fun m pn => m.insert pn.1 pn.2) pend
  commit db t pend.toList

/-- Every binding, in key order. -/
def Db.toList (db : Db) : IO (List (Nat × ByteArray)) := do
  let t ← db.tree.get
  match t.root with
  | none => return []
  | some r => return t.toList (ofCache (← cacheAll db t ∅ r))

end RaftKV.PageFile
