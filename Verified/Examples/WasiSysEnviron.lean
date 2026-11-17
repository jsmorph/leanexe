import Verified.Wasi

/-! A command that writes its environment: the count and the size that `environ` returns, each as
eight little-endian bytes, and then the variables, each as `NAME=VALUE` followed by a zero byte.
An errno of `environ` ends the run with that errno as its status, and the status is 0 otherwise. -/

namespace Verified.Examples.WasiSysEnviron

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let found ← environ
  if found.errno != 0 then
    pure found.errno
  else
    let _ ← writeStdoutSome (wordBytes found.count)
    let _ ← writeStdoutSome (wordBytes found.size)
    let _ ← writeStdoutSome found.bytes
    pure 0

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiSysEnviron
