import Demos.RandomHistogram.Program
import Verified.Wasi
import LeanExe.Wasi.WriteAll

/-! The WASI command of the random-residue histogram.  `main` reads the arguments with `args` and N
from them with `parseN`.  It then draws N words with `randomGet`, at most 512 words, 4,096 bytes, a
call, and counts their residues into a running histogram with `tally`.  The loop's state is the
counts, the words still to draw, and the errno of a failed call, and the loop's count, `N / 512 + 1`,
exceeds the number of calls it needs.  Last, `main` writes `render` of the counts to stdout with
`writeAll` of `LeanExe/Wasi/WriteAll.lean`, which follows a short write with a write of the bytes
that remain and exits with the errno of a write that fails.

The status is the errno of `args`, 2 when `parseN` refuses the argument, the errno of a failed
`randomGet`, the errno of a failed write, 77 when the writes used up `writeAll`'s passes with
bytes unwritten, and 0 when the writes took every byte.  Every errno lies from 0 to 76, so 77
differs from 2 and from every errno that the run can return. -/

namespace Demos.RandomHistogram

open LeanExe LeanExe.Wasi Library.Numerics.Decimal.Int64Text

def main : Action UInt64 := do
  let arguments ← args
  if arguments.errno != 0 then
    pure arguments.errno
  else
    let n := parseN arguments.bytes
    if n == 0 then
      pure 2
    else
      let drawn ← Wasi.loop (n / 512 + 1) (LeanExe.build 10 fun _ => (0 : UInt64), n, (0 : UInt64))
          (fun _ state => state.2.1 != 0) fun _ state => do
        let count := min state.2.1 512
        let random ← randomGet (8 * count)
        if random.errno != 0 then
          pure (state.1, (0 : UInt64), random.errno)
        else
          pure (tally state.1 random.bytes, state.2.1 - count, (0 : UInt64))
      if drawn.2.2 != 0 then
        pure drawn.2.2
      else
        let output := render drawn.1
        let written ← writeAll output
        pure (if written < output.size then 77 else 0)

verified_compile_wasi command (main := main) :=
  [parseStep, parseN, countWord, wordAt, tally, digitCount, digitByte, appendLine, render, suffix,
    writeAll, main]

end Demos.RandomHistogram
