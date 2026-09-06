import RaftKV.Runtime.PageFile

open RaftKV RaftKV.BTree RaftKV.PageFile

def dir : System.FilePath := "/tmp/raftkv-btree-test"

/-- Padded, so the tree is more than a single leaf. -/
def val (k : Nat) : ByteArray :=
  String.toUTF8 (s!"value-{k}-" ++ String.ofList (List.replicate 180 'x'))

def run : IO Unit := do
  IO.FS.removeDirAll dir <|> pure ()
  IO.FS.createDirAll dir

  -- write, then close: everything committed must survive the process
  let db ← open' dir "kv"
  for k in (List.range 500).map (fun i => (i * 137) % 500) do
    db.put k (val k)
  let t ← db.tree.get
  IO.println s!"pages allocated: {t.next}"
  close db

  -- reopen: this is a clean restart of the process, reading only what is on disk
  let db ← open' dir "kv"
  let mut ok := true
  for k in List.range 500 do
    if (← db.get k) != some (val k) then ok := false
  IO.println s!"all 500 keys survived close/reopen: {ok}"
  IO.println s!"scan size: {(← db.toList).length}"

  -- delete every third, reopen, check
  for k in (List.range 500).filter (· % 3 == 0) do
    db.del k
  close db
  let db ← open' dir "kv"
  let l ← db.toList
  IO.println s!"after deletes: {l.length} (want {((List.range 500).filter (· % 3 != 0)).length})"
  IO.println s!"survivors correct: {l.map Prod.fst == (List.range 500).filter (· % 3 != 0)}"
  let t ← db.tree.get
  close db

  -- a crash *during* the next commit can only have scribbled at or above the
  -- high-water mark, so filling that region with garbage must change nothing
  let fd ← Posix.open' (dir / "kv.pages").toString
  for p in List.range 20 do
    Posix.pwrite fd (USize.ofNat ((t.next + p) * pageSize))
      (ByteArray.mk (Array.replicate pageSize (0xa5 : UInt8)))
  Posix.fsync fd
  Posix.close fd
  let db ← open' dir "kv"
  IO.println s!"unaffected by garbage above the high-water mark: {(← db.toList).length == l.length}"

  -- and a page the tree *does* reach, corrupted: the checksum must catch it
  -- rather than the reader following a garbage pointer
  let some root := t.root | throw (IO.userError "no root")
  let before ← readPage db root
  let fd ← Posix.open' (dir / "kv.pages").toString
  let bs ← Posix.pread fd (USize.ofNat (root * pageSize)) (USize.ofNat pageSize)
  Posix.pwrite fd (USize.ofNat (root * pageSize)) (bs.set! 64 (bs.get! 64 ^^^ 0x40))
  Posix.fsync fd
  Posix.close fd
  IO.println s!"root page read before corruption: {before.isSome}, after: {(← readPage db root).isSome} (want true, false)"
  close db

#eval run
