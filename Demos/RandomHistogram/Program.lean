import LeanExe.Dialect.Bytes
import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop
import Library.Numerics.Decimal.Int64Text.Program

/-! The pure core of the random-residue histogram in the verified compiler's dialect.

`parseN` reads the argument buffer once, byte by byte, with a state of four parts: the number of
zero bytes seen, at most 2, the value of the first argument's digits so far, whether every byte of
that argument so far is a digit and the value stays below 2^64, and whether the argument has a
byte.  A digit `d` that would bring the value `v` to `10 v + d ≥ 2^64` counts as a bad byte, and the
test `v < 1844674407370955161 ∨ (v = 1844674407370955161 ∧ d ≤ 5)` decides it without overflow,
since `2^64 - 1 = 10 · 1844674407370955161 + 5`.

`histogram` folds `countWord` over the words from ten zero counts, and `tally`, the running
histogram of the WASI command, folds `countWord` over the little-endian words of a buffer, which
`wordAt` reads by Horner's rule.  `render` pushes the decimal digits of each of the ten counts and
a newline onto an array of bytes, one to a word, with the library's `digitCount` and `digitByte`,
and builds the output buffer from that array. -/

namespace Demos.RandomHistogram

open LeanExe Library.Numerics.Decimal.Int64Text

/-- The state of `parseN` after the byte `b`, from the state `s` before it. -/
def parseStep (s : UInt64 × UInt64 × Bool × Bool) (b : UInt64) : UInt64 × UInt64 × Bool × Bool :=
  if s.1 == 0 then
    if b == 0 then (1, s.2.1, s.2.2.1, s.2.2.2) else s
  else if s.1 == 1 then
    if b == 0 then (2, s.2.1, s.2.2.1, s.2.2.2)
    else if 48 ≤ b && b ≤ 57 &&
        (s.2.1 < 1844674407370955161 || (s.2.1 == 1844674407370955161 && b ≤ 53)) then
      (1, 10 * s.2.1 + (b - 48), s.2.2.1, true)
    else (1, s.2.1, false, true)
  else s

/-- N from the argument buffer `args`, or 0 for a refusal. -/
def parseN (args : Bytes) : UInt64 :=
  let s := LeanExe.loop args.size ((0 : UInt64), (0 : UInt64), true, false) fun i s =>
    parseStep s (args.get i)
  if s.1 == 2 && s.2.2.1 && s.2.2.2 && s.2.1 != 0 then s.2.1 else 0

/-- `counts` with the count of the residue of `w` mod 10 raised by one. -/
def countWord (counts : Array UInt64) (w : UInt64) : Array UInt64 :=
  let m := w % 10
  counts.set! m.toNat (counts[m.toNat]! + 1)

/-- The counts of the words of `ws` by their residue mod 10. -/
def histogram (ws : Array UInt64) : Array UInt64 :=
  ws.foldl (fun counts w => countWord counts w) (LeanExe.build 10 fun _ => 0)

/-- The little-endian word of the eight bytes of `bytes` from position `p`, by Horner's rule from
the most significant byte, `p + 7`. -/
def wordAt (bytes : Bytes) (p : UInt64) : UInt64 :=
  LeanExe.loop 8 0 fun t w => 256 * w + bytes.get (p + 7 - t)

/-- `counts` with the residues of the little-endian words of `bytes` counted. -/
def tally (counts : Array UInt64) (bytes : Bytes) : Array UInt64 :=
  LeanExe.loop (bytes.size / 8) counts fun j c => countWord c (wordAt bytes (8 * j))

/-- `text` followed by the decimal digits of `c` and a newline, one byte to a word. -/
def appendLine (text : Array UInt64) (c : UInt64) : Array UInt64 :=
  let len := digitCount c
  (LeanExe.loop len text fun k t => t.push (digitByte c (len - 1 - k))).push 10

/-- The ten lines of `counts`. -/
def render (counts : Array UInt64) : Bytes :=
  let text := LeanExe.loop 10 (#[] : Array UInt64) fun m t => appendLine t counts[m.toNat]!
  Bytes.build text.size.toUInt64 fun i => text[i.toNat]!

end Demos.RandomHistogram
