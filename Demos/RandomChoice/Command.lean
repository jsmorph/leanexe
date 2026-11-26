module

public import Demos.RandomChoice.Program
public import Verified.Wasi
public import LeanExe.Wasi.WriteAll

@[expose] public section

/-! The WASI command of the unbiased random choice.  `main` reads the arguments with `args`, and N
and K, arguments 1 and 2, with `parseArg`.  It then runs a loop of at most `K / 128 + 3` passes
while values remain to choose and no pass has set a status: the errno of a failed call, or 78 for
a stalled write.  The loop's state is the values still to choose,
the status of a failed call, a draw buffer of 4,096 bytes, and an output buffer of 10,752 bytes,
which hold the lines of 512 values of at most 20 digits.  Each pass draws 512 words into the whole
draw buffer with `randomGet`, writes the lines of the picks of their accepted words, at most the
values that remain, into the output buffer with `putPicks`, and writes the window of the output
buffer that those lines fill with `writeAll`, which continues after short writes and exits with
the errno of a write that fails.  The loop carries both buffers through its state by moves,
`randomGet` and `putPicks` write into them in place, and `writeAll` reads the output buffer in
place.  `body_bounded` of `Budget.lean` bounds the charge of `main` by a constant: a pass charges
nothing.

The status is the errno of `args`, 2 when `parseArg` refuses N or K, the errno of a failed
`randomGet` or write, 78 when the writes of a pass took fewer bytes than offered until
`writeAll`'s passes ran out, 77 when the loop's passes ran out with values still to choose, and 0
when the passes chose and wrote K values.  Every errno lies from 0 to 76, so 77 and 78 differ from
2 and from every errno that the run can return. -/

namespace Demos.RandomChoice

open LeanExe LeanExe.Wasi Library.Numerics.Decimal.Int64Text

def main : Action UInt64 := do
  let arguments ← args
  if arguments.errno != 0 then
    pure arguments.errno
  else
    let n := parseArg arguments.bytes 1
    let k := parseArg arguments.bytes 2
    if n == 0 || k == 0 then
      pure 2
    else
      let drawn ← Wasi.loop (k / 128 + 3)
          (k, (0 : UInt64), Bytes.build 4096 fun _ => 0, Bytes.build 10752 fun _ => 0)
          (fun _ state => state.1 != 0 && state.2.1 == 0) fun _ state => do
        let random ← randomGet state.2.2.1 0 4096
        if random.errno != 0 then
          pure (state.1, random.errno, random.buffer, state.2.2.2)
        else
          let put := putPicks state.2.2.2 n random.buffer state.1
          let written ← writeAll put.1 0 put.2.1
          if written < put.2.1 then
            pure (state.1, (78 : UInt64), random.buffer, put.1)
          else
            pure (state.1 - put.2.2, (0 : UInt64), random.buffer, put.1)
      if drawn.2.1 != 0 then
        pure drawn.2.1
      else if drawn.1 != 0 then
        pure 77
      else
        pure 0

verified_compile_wasi command (main := main) :=
  [parseStep, parseArg, pick, RandomHistogram.wordAt, digitCount, digitByte, putLineBytes,
    putPicks, writeAll, main]

end Demos.RandomChoice
