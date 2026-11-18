import LeanExe.Dialect.Build
import LeanExe.Dialect.Bytes
import LeanExe.Dialect.Loop
import Library.Hashing.Words.Program

/-! The pure core of the manifest checker in the verified compiler's dialect.

`parse` reads the manifest once, position by position, with one array as its state: the position
where the current line starts, whether every line so far is in `sha256sum`'s format, and the
positions of the lines found so far, two words to a line.  A newline, or the end of the manifest
after its last byte, ends the current line, and a line of at least one byte adds its two positions
and the test `lineOk` of its format.  The state is one array, which the loop moves from pass to
pass and updates in place, since the code copies an array that a tuple holds at each pass.
`hexMatches` compares the 64 bytes of a line's digits with the 32 bytes of a digest, after a test
that the 64 bytes lie within the manifest, so that no position wraps.  `render` builds the output line from the name's bytes and the bytes of `: OK` or
`: FAILED` and a newline, which it computes from their positions, since the program has no byte
literal. -/

namespace Demos.ManifestCheck

open LeanExe Library.Hashing.Words

/-- Whether `b` is a hex digit: `0` to `9`, `a` to `f`, or `A` to `F`. -/
def isHex (b : UInt64) : Bool :=
  (48 ≤ b && b ≤ 57) || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)

/-- The value of the hex digit `b`. -/
def hexDigit (b : UInt64) : UInt64 :=
  if b ≤ 57 then b - 48 else if b ≤ 70 then b - 55 else b - 87

/-- Whether the line of `m` from position `s` to position `e`, exclusive, is in `sha256sum`'s
format. -/
def lineOk (m : Bytes) (s e : UInt64) : Bool :=
  s + 67 ≤ e && (LeanExe.loop 64 true fun i ok => ok && isHex (m.get (s + i))) &&
    m.get (s + 64) == 32 && (m.get (s + 65) == 32 || m.get (s + 65) == 42)

/-- The state of `parse` after position `i` of `m`, from the state `st` before it.  Element 0 of
the state holds the position where the current line starts, element 1 holds 1 while every line so
far is in the format and 0 afterward, and the elements from 2 on hold the positions of the lines
found so far, two to a line. -/
def parseStep (m : Bytes) (st : Array UInt64) (i : UInt64) : Array UInt64 :=
  if i == m.size || m.get i == 10 then
    let s := st[(0 : UInt64).toNat]!
    if s < i then
      let ok : UInt64 := if st[(1 : UInt64).toNat]! == 1 && lineOk m s i then 1 else 0
      (((st.set! (0 : UInt64).toNat (i + 1)).set! (1 : UInt64).toNat ok).push s).push i
    else st.set! (0 : UInt64).toNat (i + 1)
  else st

/-- The positions of the lines of the manifest `m`, or the empty array for a refused manifest. -/
def parse (m : Bytes) : Array UInt64 :=
  let st := LeanExe.loop (m.size + 1) #[0, 1] fun i st => parseStep m st i
  if st[(1 : UInt64).toNat]! == 1 && st.size.toUInt64 != 2 then
    LeanExe.build (st.size.toUInt64 - 2) fun k => st[(k + 2).toNat]!
  else #[]

/-- Byte `k` of the digest `d`, for `k` below 32. -/
def digestByte (d : Words4) (k : UInt64) : UInt64 :=
  let w := if k < 8 then d.w0 else if k < 16 then d.w1 else if k < 24 then d.w2 else d.w3
  (w >>> ((k &&& 7) <<< 3)) &&& 255

/-- Whether the 64 bytes of `m` from `start` are the hex digits of the digest `d`. -/
def hexMatches (m : Bytes) (start : UInt64) (d : Words4) : Bool :=
  if m.size < 64 || m.size - 64 < start then false
  else
    LeanExe.loop 32 true fun k ok =>
      let byte := digestByte d k
      let hi := m.get (start + 2 * k)
      let lo := m.get (start + 2 * k + 1)
      ok && (isHex hi && isHex lo && hexDigit hi == byte >>> 4 && hexDigit lo == (byte &&& 15))

/-- Byte `j` of `: OK` and a newline when `ok` holds, and of `: FAILED` and a newline otherwise. -/
def suffixByte (ok : Bool) (j : UInt64) : UInt64 :=
  if j == 0 then 58
  else if j == 1 then 32
  else if ok then (if j == 2 then 79 else if j == 3 then 75 else 10)
  else if j == 2 then 70
  else if j == 3 then 65
  else if j == 4 then 73
  else if j == 5 then 76
  else if j == 6 then 69
  else if j == 7 then 68
  else 10

/-- The output line of the file `name`. -/
def render (name : Bytes) (ok : Bool) : Bytes :=
  let n := name.size
  Bytes.build (n + (if ok then 5 else 9)) fun i =>
    if i < n then name.get i else suffixByte ok (i - n)

end Demos.ManifestCheck
