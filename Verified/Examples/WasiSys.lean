import Verified.Wasi

/-! A command that writes its arguments, their sizes, a reading of the monotonic clock, and random
bytes to stdout.  `main` reads the arguments with `args` and writes their bytes, each followed by a
zero byte.  It then writes, as eight little-endian bytes each, the argument count and size that
`argsSizesGet` reports and the time of clock 1, and last the 16 bytes of `randomGet 16`.  An errno
of a call ends the run with that errno as its status, and the status is 0 otherwise. -/

namespace Verified.Examples.WasiSys

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let arguments ← args
  if arguments.errno != 0 then
    pure arguments.errno
  else
    let _ ← writeStdoutSome arguments.bytes
    let sizes ← argsSizesGet
    if sizes.errno != 0 then
      pure sizes.errno
    else
      let _ ← writeStdoutSome (wordBytes sizes.count)
      let _ ← writeStdoutSome (wordBytes sizes.size)
      let time ← clockTimeGet 1 0
      if time.errno != 0 then
        pure time.errno
      else
        let _ ← writeStdoutSome (wordBytes time.time)
        let random ← randomGet 16
        if random.errno != 0 then
          pure random.errno
        else
          let _ ← writeStdoutSome random.bytes
          pure 0

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiSys
