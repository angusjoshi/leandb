import Lake
open Lake DSL

/-!
The build needs a C shim, so this is a Lean lakefile rather than a TOML one.

`RaftKV.Runtime.Posix` binds `fsync` and positional reads and writes, which
Lean's `IO.FS` does not expose: its `flush` is `fflush`, which reaches the
kernel but not the platter — enough to survive a process crash, not enough to
survive a power cut, and power cuts are exactly what the storage proofs are
about.
-/

package raftkv where
  version := v!"0.1.0"

target raftkv_io.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "raftkv_io.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "raftkv_io.c"
  let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2"]
  buildO oFile srcJob flags #[] "cc"

extern_lib libraftkv_io pkg := do
  let name := nameToStaticLib "raftkv_io"
  let job ← fetch <| pkg.target ``raftkv_io.o
  buildStaticLib (pkg.staticLibDir / name) #[job]

@[default_target]
lean_lib RaftKV where
  -- so that `#eval` in the test files can call the C shim through the interpreter
  precompileModules := true

@[default_target]
lean_exe raftkv where
  root := `Main
