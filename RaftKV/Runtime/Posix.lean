/-!
# The POSIX primitives Lean's `IO.FS` does not expose

`IO.FS.Handle.flush` is `fflush`: it pushes a userspace buffer into the kernel
and returns. That survives a process crash — the kernel keeps the buffers — and
it does **not** survive a power cut, which is the failure the storage proofs are
about. `fsync` is the missing piece.

`fsync` needs a file descriptor, so these bindings work with descriptors
throughout rather than with Lean's opaque `Handle`. Positional reads and writes
come along for free, which is what lets the store use the two-region-plus-root
layout that `RaftKV.Storage.Persist` describes instead of rewriting whole files.

On macOS, plain `fsync` may return while the data is still in the drive's write
cache; the shim asks for `F_FULLFSYNC` first and falls back.

**Trusted.** This is a thin wrapper over `open`, `pread`, `pwrite`, `fsync` and
`close`, and it is where the disk model's assumptions meet the operating system.
-/

namespace RaftKV.Posix

/-- A file descriptor. -/
abbrev Fd := UInt32

/-- Open for reading and writing, creating the file if it does not exist. -/
@[extern "raftkv_open"]
opaque open' (path : @& String) : IO Fd

/-- Close a descriptor. -/
@[extern "raftkv_close"]
opaque close (fd : Fd) : IO Unit

/--
Force everything written to this descriptor all the way to stable storage.

This is the `flush` of `RaftKV.Disk.Op.sync`, and the reason the commit below it
is crash-safe rather than merely crash-consistent.
-/
@[extern "raftkv_fsync"]
opaque fsync (fd : Fd) : IO Unit

/-- Write a buffer in full at an offset. -/
@[extern "raftkv_pwrite"]
opaque pwrite (fd : Fd) (off : USize) (buf : @& ByteArray) : IO Unit

/-- Read up to `len` bytes from an offset; a short read at end of file is not an error. -/
@[extern "raftkv_pread"]
opaque pread (fd : Fd) (off : USize) (len : USize) : IO ByteArray

/-- Force a directory entry — a rename or a creation — to stable storage. -/
@[extern "raftkv_fsync_dir"]
opaque fsyncDir (path : @& String) : IO Unit

end RaftKV.Posix
