import Demos.RandomHistogram.Program
import Verified.Wasi

/-! The WASI command of the random-residue histogram.  `main` reads the arguments with `args` and N
from them with `parseN`.  It then draws N words with `randomGet`, at most 512 words, 4,096 bytes, a
call, and counts their residues into a running histogram with `tally`.  The loop's state is the
counts, the words still to draw, and the errno of a failed call, and the loop's count, `N / 512 + 1`,
exceeds the number of calls it needs.  Last, `main` writes `render` of the counts to stdout in one
write.  The status is the errno of `args`, 2 when `parseN` refuses the argument, the errno of a
failed `randomGet`, or the errno of the write, which is 0 on success. -/

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
        let written ← writeStdoutSome (render drawn.1)
        pure written.errno

verified_compile_wasi command (main := main) :=
  [parseStep, parseN, countWord, wordAt, tally, digitCount, digitByte, appendLine, render, main]

end Demos.RandomHistogram
