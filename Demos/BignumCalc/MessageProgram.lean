module

public import Library.Numerics.Bignum.Program
public import LeanExe.Dialect.Bytes

@[expose] public section

/-!
# The calculator of the bare-metal program and the AArch64 Image

The bare-metal program and the Image each read one message of ASCII text and write one line.  A
message names an operation, `neg`, `cmp`, `add`, `sub`, `mul`, `tdiv`, `tmod`, `ediv`, or `emod`,
followed by a space and the first operand, and for every operation but `neg` by a space and the
second operand, as in `mul 123 -456`.  `calcLine` takes the message's bytes one to a word, splits
it at its spaces, runs the text export of the operation on the operands, and returns the line's
bytes one to a word: `0`, a space, and the result's text for the status 0, and otherwise the
status's digit alone, `1` or `2` for a first or second operand outside the grammar, `3` for a
division by zero, and `4` for a message longer than 65,536 bytes, an unknown name, or wrong
separators: a number of spaces other than the operation's, or an empty part, from a leading, a
trailing, or a doubled space.  `cmp` writes `-1`, `0`, or `1` as its result.

`calcWords` is the bare-metal program's entry.  It takes the message's bytes packed eight to a
word, the lowest first, with the byte count, as leanexe's `inMain` passes them, and returns the
line's bytes packed the same way, with zeros after the last byte of the last word.  `calcBytes` is
the Image's entry, on `LeanExe.Bytes`.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open LeanExe

/-- The position of the first space (32) among the words of `m` at or after `s`, or the size of
`m` when there is none. -/
@[inline] def nextSpace (m : Array UInt64) (s : UInt64) : UInt64 :=
  LeanExe.loop m.size.toUInt64 m.size.toUInt64 fun i p =>
    if p == m.size.toUInt64 && s ≤ i && m[i.toNat]! == 32 then i else p

/-- Whether the first `p` words of `m` are the three bytes `c0`, `c1`, `c2`. -/
@[inline] def name3 (m : Array UInt64) (p c0 c1 c2 : UInt64) : Bool :=
  p == 3 && m[(0 : UInt64).toNat]! == c0 && m[(1 : UInt64).toNat]! == c1 &&
    m[(2 : UInt64).toNat]! == c2

/-- Whether the first `p` words of `m` are the four bytes `c0` to `c3`. -/
@[inline] def name4 (m : Array UInt64) (p c0 c1 c2 c3 : UInt64) : Bool :=
  p == 4 && m[(0 : UInt64).toNat]! == c0 && m[(1 : UInt64).toNat]! == c1 &&
    m[(2 : UInt64).toNat]! == c2 && m[(3 : UInt64).toNat]! == c3

/-- The operation that the first `p` words of `m` name: 1 to 9 for `neg`, `cmp`, `add`, `sub`,
`mul`, `tdiv`, `tmod`, `ediv`, and `emod`, and 0 for any other name. -/
@[inline] def opCode (m : Array UInt64) (p : UInt64) : UInt64 :=
  if name3 m p 110 101 103 then 1
  else if name3 m p 99 109 112 then 2
  else if name3 m p 97 100 100 then 3
  else if name3 m p 115 117 98 then 4
  else if name3 m p 109 117 108 then 5
  else if name4 m p 116 100 105 118 then 6
  else if name4 m p 116 109 111 100 then 7
  else if name4 m p 101 100 105 118 then 8
  else if name4 m p 101 109 111 100 then 9
  else 0

/-- The line of a status and a text: `0`, a space, and the text for the status 0, and the
status's digit alone otherwise. -/
@[inline] def line (st : UInt64) (t : Array UInt64) : Array UInt64 :=
  if st == 0 then
    LeanExe.build (t.size.toUInt64 + 2) fun i =>
      if i == 0 then 48 else if i == 1 then 32 else t[(i - 2).toNat]!
  else #[48 + st]

/-- The text of a comparison's code: `-1`, `0`, or `1` for the codes 0, 1, and 2. -/
@[inline] def cmpText (c : UInt64) : Array UInt64 :=
  if c == 0 then #[45, 49] else if c == 1 then #[48] else #[49]

/-- The line of the message `m`, whose bytes are its words. -/
def calcLine (m : Array UInt64) : Array UInt64 :=
  let n := m.size.toUInt64
  if 65536 < n then #[52]
  else
    let p1 := nextSpace m 0
    let p2 := nextSpace m (p1 + 1)
    let p3 := nextSpace m (p2 + 1)
    let op := opCode m p1
    if op == 1 then
      if p1 + 1 < n && p2 == n then
        let r := textNeg (slice m (p1 + 1) (n - p1 - 1))
        line r.1 r.2
      else #[52]
    else if op == 0 || p2 == n || p3 != n || p2 ≤ p1 + 1 || n ≤ p2 + 1 then #[52]
    else
      let a := slice m (p1 + 1) (p2 - p1 - 1)
      let b := slice m (p2 + 1) (n - p2 - 1)
      if op == 2 then
        let r := textCmp a b
        let t := cmpText r.2
        line r.1 t
      else
        let r := if op == 3 then textAdd a b
          else if op == 4 then textSub a b
          else if op == 5 then textMul a b
          else if op == 6 then textTDiv a b
          else if op == 7 then textTMod a b
          else if op == 8 then textEDiv a b
          else textEMod a b
        line r.1 r.2

/-- The `n` bytes of a message packed eight to a word, the lowest first, one to a word. -/
def unpack (ws : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.build n fun i => (ws[(i / 8).toNat]! >>> (8 * (i % 8))) &&& 255

/-- The words of `l`, whose words hold one byte each, packed eight to a word, the lowest first, with
zeros after the last. -/
def pack (l : Array UInt64) : Array UInt64 :=
  LeanExe.build ((l.size.toUInt64 + 7) / 8) fun k =>
    l[(8 * k).toNat]! + (l[(8 * k + 1).toNat]! <<< 8) + (l[(8 * k + 2).toNat]! <<< 16) +
      (l[(8 * k + 3).toNat]! <<< 24) + (l[(8 * k + 4).toNat]! <<< 32) +
      (l[(8 * k + 5).toNat]! <<< 40) + (l[(8 * k + 6).toNat]! <<< 48) +
      (l[(8 * k + 7).toNat]! <<< 56)

/-- The bare-metal program's entry: the packed line of the message of `len` bytes packed in `ws`. -/
def calcWords (ws : Array UInt64) (len : UInt64) : Array UInt64 :=
  pack (if 65536 < len then #[52] else calcLine (unpack ws len))

/-- The Image's entry: the line of the message `b`. -/
def calcBytes (b : Bytes) : Bytes :=
  let out := calcLine (LeanExe.build b.size fun i => b.get i)
  Bytes.build out.size.toUInt64 fun j => out[j.toNat]!

end Demos.BignumCalc
