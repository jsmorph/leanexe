import Verified.Wasi

/-! A command that writes what the host answers about the preopened directory, each number as
eight little-endian bytes: the errno, the tag, and the name's length of `fd_prestat_get`, then the
errno of `fd_prestat_dir_name` into a buffer of 0 bytes, and the errno and the buffer of
`fd_prestat_dir_name` into buffers of 1 and of 2 bytes.  The status is 0. -/

namespace Verified.Examples.WasiPrestat

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let record ← fdPrestatGet .preopened
  let _ ← writeStdoutSome (wordBytes record.errno)
  let _ ← writeStdoutSome (wordBytes record.tag)
  let _ ← writeStdoutSome (wordBytes record.prNameLen)
  let empty ← fdPrestatDirName .preopened 0
  let _ ← writeStdoutSome (wordBytes empty.errno)
  let one ← fdPrestatDirName .preopened 1
  let _ ← writeStdoutSome (wordBytes one.errno)
  let _ ← writeStdoutSome one.bytes
  let two ← fdPrestatDirName .preopened 2
  let _ ← writeStdoutSome (wordBytes two.errno)
  let _ ← writeStdoutSome two.bytes
  pure 0

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiPrestat
