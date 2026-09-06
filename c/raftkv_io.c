/*
 * POSIX file primitives that Lean's `IO.FS` does not expose.
 *
 * `IO.FS.Handle.flush` is `fflush`: it pushes a userspace buffer into the
 * kernel and returns. That is enough to survive a process crash and not enough
 * to survive a power cut, which is the failure the storage proofs are about.
 * `fsync` is the missing piece, and it needs a file descriptor, so this shim
 * works with descriptors throughout rather than with Lean's `Handle`.
 *
 * Positional reads and writes come along for free, which is also what lets the
 * store use the two-region-plus-root layout the proof describes instead of
 * rewriting whole files.
 *
 * Errors are returned as Lean IO errors carrying `strerror(errno)`.
 */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

static lean_obj_res raftkv_errno(const char *what) {
  char buf[256];
  snprintf(buf, sizeof buf, "%s: %s", what, strerror(errno));
  return lean_io_result_mk_error(
    lean_mk_io_user_error(lean_mk_string(buf)));
}

/* open : String → IO UInt32 — read/write, created if absent. */
LEAN_EXPORT lean_obj_res raftkv_open(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  int fd = open(lean_string_cstr(path), O_RDWR | O_CREAT, 0644);
  if (fd < 0) return raftkv_errno("open");
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* close : UInt32 → IO Unit */
LEAN_EXPORT lean_obj_res raftkv_close(uint32_t fd, lean_obj_arg w) {
  (void)w;
  if (close((int)fd) < 0) return raftkv_errno("close");
  return lean_io_result_mk_ok(lean_box(0));
}

/* fsync : UInt32 → IO Unit — the whole point of this file. */
LEAN_EXPORT lean_obj_res raftkv_fsync(uint32_t fd, lean_obj_arg w) {
  (void)w;
#if defined(__APPLE__)
  /* On macOS plain fsync may leave data in the drive's write cache;
     F_FULLFSYNC is the one that actually reaches the platter. */
  if (fcntl((int)fd, F_FULLFSYNC, 0) < 0) {
    if (fsync((int)fd) < 0) return raftkv_errno("fsync");
  }
#else
  if (fsync((int)fd) < 0) return raftkv_errno("fsync");
#endif
  return lean_io_result_mk_ok(lean_box(0));
}

/* pwrite : UInt32 → USize → ByteArray → IO Unit — write in full at an offset. */
LEAN_EXPORT lean_obj_res raftkv_pwrite(uint32_t fd, size_t off, b_lean_obj_arg buf,
                                       lean_obj_arg w) {
  (void)w;
  const uint8_t *p = lean_sarray_cptr(buf);
  size_t len = lean_sarray_size(buf);
  size_t done = 0;
  while (done < len) {
    ssize_t n = pwrite((int)fd, p + done, len - done, (off_t)(off + done));
    if (n < 0) {
      if (errno == EINTR) continue;
      return raftkv_errno("pwrite");
    }
    if (n == 0) break;
    done += (size_t)n;
  }
  if (done != len) return raftkv_errno("pwrite (short)");
  return lean_io_result_mk_ok(lean_box(0));
}

/* pread : UInt32 → USize → USize → IO ByteArray — short reads are not an error. */
LEAN_EXPORT lean_obj_res raftkv_pread(uint32_t fd, size_t off, size_t len,
                                      lean_obj_arg w) {
  (void)w;
  lean_object *arr = lean_alloc_sarray(1, len, len);
  uint8_t *p = lean_sarray_cptr(arr);
  size_t done = 0;
  while (done < len) {
    ssize_t n = pread((int)fd, p + done, len - done, (off_t)(off + done));
    if (n < 0) {
      if (errno == EINTR) continue;
      lean_free_object(arr);
      return raftkv_errno("pread");
    }
    if (n == 0) break; /* end of file */
    done += (size_t)n;
  }
  lean_sarray_set_size(arr, done);
  return lean_io_result_mk_ok(arr);
}

/* fsyncDir : String → IO Unit — makes a rename or creation durable. */
LEAN_EXPORT lean_obj_res raftkv_fsync_dir(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  int fd = open(lean_string_cstr(path), O_RDONLY);
  if (fd < 0) return raftkv_errno("open dir");
  int rc = fsync(fd);
  int e = errno;
  close(fd);
  if (rc < 0) { errno = e; return raftkv_errno("fsync dir"); }
  return lean_io_result_mk_ok(lean_box(0));
}
