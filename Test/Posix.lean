import RaftKV
open RaftKV.Posix

/-! Exercise the POSIX bindings: positional IO, short reads, and `fsync`. -/
def probe : IO (List Nat × List Nat × List Nat) := do
  let fd ← open' "/tmp/raftkv-posix-probe.bin"
  pwrite fd 0 (ByteArray.mk #[1,2,3,4])
  pwrite fd 16 (ByteArray.mk #[9,9])
  fsync fd
  let a ← pread fd 0 4
  let b ← pread fd 16 2
  let c ← pread fd 100 8   -- past the end: a short read, not an error
  close fd
  fsyncDir "/tmp"
  return (a.toList.map (·.toNat), b.toList.map (·.toNat), c.toList.map (·.toNat))

#eval probe
