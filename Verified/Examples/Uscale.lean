import Verified.Reflect.Command

/-! Natural numbers of any size as arrays of 32-bit limbs, least significant first, each limb held
in a 64-bit word, and the exact unrounded scaling that the decimal parsers and printers use.  A
32-bit limb keeps every intermediate product of a limb by a word below `2 ^ 32` inside one word:
`(2 ^ 32 - 1) ^ 2 + 2 · (2 ^ 32 - 1) = 2 ^ 64 - 1`.  The arrays may carry zero limbs at the top.
`mulSmall` multiplies by a word below `2 ^ 32` and adds one, `shl` multiplies by a power of two,
`le` compares, `sub` subtracts a smaller number, `bitLen` gives the bit length, and `divBits`
divides by restoring division when the quotient has at most `bits ≤ 63` bits.  `scaledQuot n d sn
sd bits` is the quotient `⌊n · 2 ^ sn / (d · 2 ^ sd)⌋` with a flag for a nonzero remainder: the
unrounded scaling of Cox ("Floating-Point Printing and Parsing Can Be Simple And Fast", 2026)
computed with exact integers, from which a rounding to any format, a floor, or a ceiling follows.
`UscaleTheorem` states each function's value as a natural number. -/

namespace Verified.Examples.Uscale

/-- `a · m + c` for limbs `a` and words `m, c < 2 ^ 32`; one limb longer than `a`. -/
def mulSmall (a : Array UInt64) (m c : UInt64) : Array UInt64 :=
  let s := LeanExe.loop a.size.toUInt64 (LeanExe.build 0 fun _ => (0 : UInt64), c)
    fun i (s : Array UInt64 × UInt64) =>
    let t := a[i.toNat]! * m + s.2
    (s.1.push (t &&& 0xFFFFFFFF), t >>> 32)
  s.1.push s.2

/-- Limb `i` of `a · 2 ^ (32 q + r)` for `r < 32`. -/
def shlLimb (a : Array UInt64) (q r i : UInt64) : UInt64 :=
  if i < q then 0
  else if r == 0 then a[(i - q).toNat]!
  else ((a[(i - q).toNat]! <<< r) &&& 0xFFFFFFFF) ||| (a[(i - q - 1).toNat]! >>> (32 - r))

/-- `a · 2 ^ k`; `k / 32 + 1` limbs longer than `a`. -/
def shl (a : Array UInt64) (k : UInt64) : Array UInt64 :=
  LeanExe.build (a.size.toUInt64 + (k >>> 5) + 1) fun i => shlLimb a (k >>> 5) (k &&& 31) i

/-- The outcome of comparing limb `j` of `a` and `b` after the limbs above it: 0 while equal, 1
when `a` is smaller, 2 when `a` is larger. -/
def cmpStep (a b : Array UInt64) (j s : UInt64) : UInt64 :=
  if s != 0 then s
  else if a[j.toNat]! < b[j.toNat]! then 1
  else if b[j.toNat]! < a[j.toNat]! then 2 else 0

/-- Whether `a ≤ b`, comparing limbs from the top. -/
def le (a b : Array UInt64) : Bool :=
  let n := max a.size.toUInt64 b.size.toUInt64
  LeanExe.loop n (0 : UInt64) (fun i s => cmpStep a b (n - 1 - i) s) != 2

/-- `a - b` for `b ≤ a`, as many limbs as `a`. -/
def sub (a b : Array UInt64) : Array UInt64 :=
  (LeanExe.loop a.size.toUInt64 (LeanExe.build 0 fun _ => (0 : UInt64), (0 : UInt64))
    fun i (s : Array UInt64 × UInt64) =>
    let d : UInt64 := a[i.toNat]! + 0x100000000 - b[i.toNat]! - s.2
    (s.1.push (d &&& 0xFFFFFFFF), (1 : UInt64) - (d >>> 32))).1

/-- The bit length of a word, by binary search. -/
def wordBits (x : UInt64) : UInt64 :=
  let (x, n) := if x >>> 32 != 0 then (x >>> 32, (32 : UInt64)) else (x, (0 : UInt64))
  let (x, n) := if x >>> 16 != 0 then (x >>> 16, n + 16) else (x, n)
  let (x, n) := if x >>> 8 != 0 then (x >>> 8, n + 8) else (x, n)
  let (x, n) := if x >>> 4 != 0 then (x >>> 4, n + 4) else (x, n)
  let (x, n) := if x >>> 2 != 0 then (x >>> 2, n + 2) else (x, n)
  if x >>> 1 != 0 then n + 2 else n + x

/-- The bit length of `a`, 0 for zero. -/
def bitLen (a : Array UInt64) : UInt64 :=
  LeanExe.loop a.size.toUInt64 (0 : UInt64) fun i s =>
    if a[i.toNat]! != 0 then 32 * i + wordBits a[i.toNat]! else s

/-- One step of restoring division: the quotient bit `j` and the remainder. -/
def divStep (d : Array UInt64) (j : UInt64) (s : UInt64 × Array UInt64) : UInt64 × Array UInt64 :=
  let t := shl d j
  if le t s.2 then (s.1 ||| ((1 : UInt64) <<< j), sub s.2 t) else s

/-- The quotient of `n` by `d` and the remainder, when the quotient is below `2 ^ bits`. -/
def divBits (n d : Array UInt64) (bits : UInt64) : UInt64 × Array UInt64 :=
  LeanExe.loop bits ((0 : UInt64), n) fun i s => divStep d (bits - 1 - i) s

/-- `⌊n · 2 ^ sn / (d · 2 ^ sd)⌋` below `2 ^ bits`, and whether the division leaves a
remainder. -/
def scaledQuot (n d : Array UInt64) (sn sd bits : UInt64) : UInt64 × Bool :=
  let r := divBits (shl n sn) (shl d sd) bits
  (r.1, bitLen r.2 != 0)

/-- `10 ^ k` for `k ≤ 19`. -/
def pow10Word (k : UInt64) : UInt64 := LeanExe.loop k 1 fun _ x => 10 * x

/-- `10 ^ k` as limbs, by factors of `10 ^ 9`. -/
def pow10 (k : UInt64) : Array UInt64 :=
  mulSmall (LeanExe.loop (k / 9) (LeanExe.build 1 fun _ => (1 : UInt64))
    fun _ a => mulSmall a 1000000000 0) (pow10Word (k % 9)) 0

verified_compile compiled := [mulSmall, shlLimb, shl, cmpStep, le, sub, wordBits, bitLen,
  divStep, divBits, scaledQuot, pow10Word, pow10]

end Verified.Examples.Uscale
