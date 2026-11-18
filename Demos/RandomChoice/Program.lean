import LeanExe.Dialect.Bytes
import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop
import Library.Numerics.Decimal.Int64Text.Program
import Demos.RandomHistogram.Program

/-! The pure core of the unbiased random choice in the verified compiler's dialect.

`parseArg` reads the argument buffer once, byte by byte, with a state of four parts: the number of
zero bytes seen, the value of the digits of argument `index` so far, whether every byte of that
argument so far is a digit and the value stays below 2^64, and whether the argument has a byte.  A
digit `d` that would bring the value `v` to `10 v + d ≥ 2^64` counts as a bad byte, and the test
`v < 1844674407370955161 ∨ (v = 1844674407370955161 ∧ d ≤ 5)` decides it without overflow, since
`2^64 - 1 = 10 · 1844674407370955161 + 5`.  A buffer holds fewer than 2^64 bytes, so the count of
zero bytes does not wrap.

`pick` accepts `w` when `n ≠ 0` and `w ≥ (0 - n) % n`, the word `2^64 mod n`, since
`0 - n = 2^64 - n` in word arithmetic, and returns `w % n + 1`, at most `n`.

`render` computes the size of the text, `textSize`, builds an array of that many words, and folds
`putLine` over the values, which writes the decimal digits of each value and a newline into the
array, one byte to a word, from the position after the previous line.  It then builds the output
buffer from the array.  The array is one block, written in place, so the generated bound charges
its block once, where an array that grew by a push for each byte would be charged for each push. -/

namespace Demos.RandomChoice

open LeanExe Library.Numerics.Decimal.Int64Text

/-- The state of `parseArg` after the byte `b`, from the state `s` before it, for argument
`index`. -/
def parseStep (index : UInt64) (s : UInt64 × UInt64 × Bool × Bool) (b : UInt64) :
    UInt64 × UInt64 × Bool × Bool :=
  if b == 0 then (s.1 + 1, s.2.1, s.2.2.1, s.2.2.2)
  else if s.1 == index then
    if 48 ≤ b && b ≤ 57 &&
        (s.2.1 < 1844674407370955161 || (s.2.1 == 1844674407370955161 && b ≤ 53)) then
      (s.1, 10 * s.2.1 + (b - 48), s.2.2.1, true)
    else (s.1, s.2.1, false, true)
  else s

/-- The value of argument `index` of the argument buffer `args`, or 0 for a refusal. -/
def parseArg (args : Bytes) (index : UInt64) : UInt64 :=
  let s := LeanExe.loop args.size ((0 : UInt64), (0 : UInt64), true, false) fun i s =>
    parseStep index s (args.get i)
  if index < s.1 && s.2.2.1 && s.2.2.2 && s.2.1 != 0 then s.2.1 else 0

/-- The value in [1, n] of the word `w`, or 0 when `w` is rejected. -/
def pick (n w : UInt64) : UInt64 :=
  if n != 0 && (0 - n) % n ≤ w then w % n + 1 else 0

/-- The picks of the accepted little-endian words of `bytes` for the range [1, n], in order, at most
`limit` of them.  The random histogram's `wordAt` reads each word. -/
def choose (n : UInt64) (bytes : Bytes) (limit : UInt64) : Array UInt64 :=
  LeanExe.loop (bytes.size / 8) (#[] : Array UInt64) fun j picks =>
    let v := pick n (RandomHistogram.wordAt bytes (8 * j))
    if v != 0 && picks.size.toUInt64 < limit then picks.push v else picks

/-- The number of bytes of the lines of `values`: the digits of each value and a newline. -/
def textSize (values : Array UInt64) : UInt64 :=
  values.foldl (fun total v => total + digitCount v + 1) 0

/-- `text` with the line of `v`, its decimal digits and a newline, written from position `pos`. -/
def putLine (text : Array UInt64) (pos v : UInt64) : Array UInt64 :=
  let len := digitCount v
  (LeanExe.loop len text fun k t => t.set! (pos + k).toNat (digitByte v (len - 1 - k))).set!
    (pos + len).toNat 10

/-- The lines of `values`. -/
def render (values : Array UInt64) : Bytes :=
  let total := textSize values
  let filled := values.foldl (fun s v => (putLine s.1 s.2 v, s.2 + digitCount v + 1))
    (LeanExe.build total fun _ => (0 : UInt64), (0 : UInt64))
  Bytes.build total fun i => filled.1[i.toNat]!

end Demos.RandomChoice
