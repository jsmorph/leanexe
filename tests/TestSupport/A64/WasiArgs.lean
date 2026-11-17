import Verified.Wasi

/-!
A command that writes its arguments, for the runs of the stubs of `args_sizes_get` and `args_get`
in `tests/linux/a64-wasi.sh`: the count and the size that `args` returns, each as eight
little-endian bytes, and then the arguments, each followed by a zero byte.  An errno of `args` ends
the run with that errno as its status, and the status is 0 otherwise.
-/

namespace TestSupport.A64.WasiArgs

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let found ← args
  if found.errno != 0 then
    pure found.errno
  else
    let _ ← writeStdoutSome (wordBytes found.count)
    let _ ← writeStdoutSome (wordBytes found.size)
    let _ ← writeStdoutSome found.bytes
    pure 0

verified_compile_wasi command (main := main) := [wordBytes, main]

end TestSupport.A64.WasiArgs
