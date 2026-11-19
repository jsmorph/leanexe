import Verified.Wasi

/-! A command that reads three clocks and two buffers of random bytes and writes what they gave to
stdout.  `main` reads clock 0 (realtime), clock 1 (monotonic), and clock 2 (process CPU time), and
writes, as eight little-endian bytes each, the errno and time of the first two and the errno of
the third.  It then fills buffers of 16 and 5,000 bytes with `randomGet` and writes, for each, the
errno as eight little-endian bytes and the buffer.  The status is 0. -/

namespace Verified.Examples.WasiClockRandom

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let wall ← clockTimeGet 0 0
  let _ ← writeStdoutSome (wordBytes wall.errno)
  let _ ← writeStdoutSome (wordBytes wall.time)
  let time ← clockTimeGet 1 0
  let _ ← writeStdoutSome (wordBytes time.errno)
  let _ ← writeStdoutSome (wordBytes time.time)
  let cpu ← clockTimeGet 2 0
  let _ ← writeStdoutSome (wordBytes cpu.errno)
  let small ← randomGet (Bytes.build 16 fun _ => 0) 0 16
  let _ ← writeStdoutSome (wordBytes small.errno)
  let _ ← writeStdoutSome small.buffer
  let large ← randomGet (Bytes.build 5000 fun _ => 0) 0 5000
  let _ ← writeStdoutSome (wordBytes large.errno)
  let _ ← writeStdoutSome large.buffer
  pure 0

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiClockRandom
