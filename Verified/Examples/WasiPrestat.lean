import Verified.Wasi

/-! A command that writes what the host answers about the preopened directory, each number as
eight little-endian bytes: the errno, the tag, and the name's length of `fd_prestat_get`, and then,
for buffers of 0, 1, and 2 bytes, the errno of `fd_prestat_dir_name` and the buffer, whose bytes
are 0 after an errno.  The status is 0.  Each call lies in a function of its own. -/

namespace Verified.Examples.WasiPrestat

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

/-- Writes the errno and the fields of the record of the preopened directory. -/
def record : Action UInt64 := do
  let found ← fdPrestatGet .preopened
  let _ ← writeStdoutSome (wordBytes found.errno)
  let _ ← writeStdoutSome (wordBytes found.tag)
  let _ ← writeStdoutSome (wordBytes found.prNameLen)
  pure found.errno

/-- Writes the errno and the buffer of the preopened directory's name into `capacity` bytes. -/
def name (capacity : UInt64) : Action UInt64 := do
  let found ← fdPrestatDirName .preopened (Bytes.build capacity fun _ => 0) 0 capacity
  let _ ← writeStdoutSome (wordBytes found.errno)
  let _ ← writeStdoutSome found.buffer
  pure found.errno

def main : Action UInt64 := do
  let _ ← record
  let _ ← name 0
  let _ ← name 1
  let _ ← name 2
  pure 0

verified_compile_wasi command (main := main) := [wordBytes, record, name, main]

end Verified.Examples.WasiPrestat
