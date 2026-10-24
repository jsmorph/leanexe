import Verified.Wasi

namespace StdioExample
open LeanExe LeanExe.Wasi

def copySome (capacity : UInt64) : Action UInt64 := do
  let input ← readSome capacity
  if input.errno != 0 then
    pure input.errno
  else
    let output ← writeStdoutSome input.bytes
    pure output.errno

def main : Action UInt64 := copySome 4096

verified_compile_wasi callable := [copySome, main]
verified_compile_wasi command (main := main) := [copySome, main]
end StdioExample
