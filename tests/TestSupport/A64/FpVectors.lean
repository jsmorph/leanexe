import TestSupport.A64.Cosim
import LeanExe.A64.Startup
import LeanExe.A64.Table

/-!
The test of the floating-point forms' meanings: for `FADD`, `FSUB`, `FMUL`, `FDIV`, `FSQRT`,
`UCVTF`, and `FCMP`, vectors of operand words that stress the corner cases of IEEE 754, an arm64
Image that runs each form on each vector and writes each result's word to the UART, and a check of
every result word against the model, whose forms compute Talos's functions.  `FCMP` runs as the
generator's three comparisons, `f64Eq`, `f64Lt`, and `f64Le`, on the same operands, whose results
form bits 0, 1, and 2 of the result word.

A form's vectors fall into classes, each of which receives an equal share of the form's count,
with the remainder to the last class, and each class draws its operands from SplitMix64.  A
binary class of `FSUB` is the class of `FADD` with the second operand's sign changed, so that both
forms compute the same exact sums.  `image` writes the Image: the header, the startup of
`LeanExe.A64.Startup`, which enables floating point and writes FPCR as `fpcrValue` as the back
end's Images do, the program `mainCode`, the vector and translation tables, and the operand words
at the area.  For each form, `mainCode` loads each vector's words into X2 and X3, runs the code
that the generator emits for the form (`fBin`, `sqrtCode`, `convertCode`, or `fCmp`), and stores
the eight bytes of the result in X2 to the UART, lowest first.  `checkRun` reads the operands from
the Image's bytes and the results from the UART's bytes and compares each result with the model's
run of the same code, and `tagsOf` classifies each vector's exact result by its position on the
grid of doubles, or a comparison's operands as unordered, equal, less, or greater.
-/

namespace TestSupport.A64.Fp

open LeanExe.A64
open LeanExe (roundUp)

/-- The forms under test. -/
inductive Form where
  | fadd | fsub | fmul | fdiv | fsqrt | ucvtf | fcmp
  deriving BEq, Repr, Inhabited

def Form.all : List Form := [.fadd, .fsub, .fmul, .fdiv, .fsqrt, .ucvtf, .fcmp]

def Form.name : Form → String
  | .fadd => "fadd" | .fsub => "fsub" | .fmul => "fmul" | .fdiv => "fdiv" | .fsqrt => "fsqrt"
  | .ucvtf => "ucvtf" | .fcmp => "fcmp"

def Form.ofName (s : String) : Option Form := Form.all.find? (·.name == s)

def Form.binary : Form → Bool
  | .fsqrt | .ucvtf => false
  | _ => true

/-- The code that the generator emits for the form on the words in X2 and X3, which leaves the
result's word in X2.  For `FCMP` it is the code of `f64Eq` on a copy of X2 in X4 and on X3, of
`f64Lt` on a copy in X7 and on X3, and of `f64Le` on X2 and X3, followed by additions that leave
`4 le + 2 lt + eq` in X2: the result of `f64Eq` in bit 0, of `f64Lt` in bit 1, and of `f64Le` in
bit 2. -/
def Form.code : Form → List Instr
  | .fadd => fBin .fadd 2 3
  | .fsub => fBin .fsub 2 3
  | .fmul => fBin .fmul 2 3
  | .fdiv => fBin .fdiv 2 3
  | .fsqrt => sqrtCode 2
  | .ucvtf => convertCode 2
  | .fcmp => [mov 4 2] ++ fCmp 1 4 3 ++ [mov 7 2] ++ fCmp 5 7 3 ++ fCmp 8 2 3 ++
      [.addReg 2 2 2, .addReg 2 2 7, .addReg 2 2 2, .addReg 2 2 4]

/-- X2 after the model runs the form's code from a state with `a` in X2 and `b` in X3. -/
def Form.model (f : Form) (a b : UInt64) : Option UInt64 := do
  let s : State :=
    { regs := fun r => if r.val = 2 then a else if r.val = 3 then b else 0, dregs := fun _ => 0,
      sp := 0, pc := 0, nFlag := false, zFlag := false, cFlag := false, vFlag := false,
      mem := fun _ => 0, out := [] }
  let P : Platform := { normal := fun _ => false, uart := uartAddr }
  let t ← f.code.foldlM (fun s i => exec P i s) s
  return t.regs 2

/-! ## Drawing numbers -/

def coin : Gen Bool := return (← below 2) = 0

/-- A number of `k` random bits, `k` at most 64. -/
def bits (k : Nat) : Gen Nat := return (← word).toNat % 2 ^ k

/-- A number from `lo` to `hi`, both included. -/
def between (lo hi : Nat) : Gen Nat := return lo + (← below (hi + 1 - lo))

def irange (lo hi : Int) : Gen Int := return lo + Int.ofNat (← below (hi + 1 - lo).toNat)

/-- An odd number of exactly `k` bits, `k` from 1 to 64. -/
def oddWith (k : Nat) : Gen Nat :=
  if k ≤ 1 then return 1 else return 2 ^ (k - 1) + 2 * (← bits (k - 2)) + 1

/-- A significand of 53 bits, the top one set. -/
def sig : Gen Nat := return 2 ^ 52 + (← bits 52)

/-- A nonzero number from `-2^20` to `2^20`. -/
def small : Gen Int := do
  let k := Int.ofNat (← between 1 (2 ^ 20))
  return if ← coin then k else -k

/-- The word with sign `neg`, exponent field `e`, and fraction `f`. -/
def dbl (neg : Bool) (e f : Nat) : UInt64 :=
  UInt64.ofNat ((if neg then 2 ^ 63 else 0) + e * 2 ^ 52 + f)

def negW (w : UInt64) : UInt64 := w ^^^ 0x8000000000000000

/-- The double `m * 2^q`, rounded by Talos's encoding of a magnitude in units of `2^-1074`; exact
when `m` has at most 53 significant bits, `q` is at least -1074, and the value lies below the
overflow threshold. -/
def scaled (neg : Bool) (m : Nat) (q : Int) : UInt64 :=
  Wasm.IEEE64.roundScaledMagnitude neg (m * 2 ^ (q + 1074).toNat)

/-- A word with a random sign and fraction and an exponent field from 0 to 2047. -/
def anyWord : Gen UInt64 := return dbl (← coin) (← below 2048) (← bits 52)

/-- The inverse of the odd number `a` modulo `2^64`, by Newton's iteration from `a`, which is its
own inverse modulo 8. -/
def inv64 (a : Nat) : Nat :=
  let a := UInt64.ofNat a
  let step (x : UInt64) := x * (2 - a * x)
  (step (step (step (step (step a))))).toNat

/-- A root of `y^2 ≡ c` modulo `2^n`, for `c ≡ 1` modulo 8, lifted one bit at a time from 1. -/
def sqrtMod (c n : Nat) : Nat := Id.run do
  let mut y := 1
  for i in [3:n] do
    if y * y % 2 ^ (i + 1) ≠ c % 2 ^ (i + 1) then y := y + 2 ^ (i - 1)
  return y % 2 ^ n

/-! ## Special values -/

/-- The 26 special values, by `k`: zero, infinity, the default NaN, a quiet NaN with a random
payload, a signaling NaN with a random payload, the signaling NaN of payload 1, the smallest and
largest subnormals, a random subnormal, the smallest and largest normals, 1.0, and a random
normal, each positive for even `k` and negative for odd `k`. -/
def special (k : Nat) : Gen UInt64 := do
  let p : UInt64 ← match k / 2 % 13 with
    | 0 => pure 0
    | 1 => pure 0x7FF0000000000000
    | 2 => pure 0x7FF8000000000000
    | 3 => return 0x7FF8000000000000 ||| ((← word) &&& 0x7FFFFFFFFFFFF)
    | 4 =>
        let w := (← word) &&& 0x7FFFFFFFFFFFF
        pure (0x7FF0000000000000 ||| (if w = 0 then 1 else w))
    | 5 => pure 0x7FF0000000000001
    | 6 => pure 1
    | 7 => pure 0x000FFFFFFFFFFFFF
    | 8 => return ((← word) &&& 0xFFFFFFFFFFFFF) ||| 1
    | 9 => pure 0x0010000000000000
    | 10 => pure 0x7FEFFFFFFFFFFFFF
    | 11 => pure 0x3FF0000000000000
    | _ => return dbl false (← between 1 2046) (← bits 52)
  return if k % 2 = 1 then negW p else p

/-- Every ordered pair of special values, the pair `i` modulo 676. -/
def specialPair (i : Nat) : Gen (UInt64 × UInt64) :=
  return (← special (i / 26 % 26), ← special (i % 26))

/-! ## Sums -/

/-- A random normal `a` and a `b` of either sign whose magnitude is half an ulp of `a`, half an
ulp plus or minus up to `2^20` units in `b`'s last place, or one and a half ulps: sums at a tie
or within `2^-33` ulp of one. -/
def addTie (_ : Nat) : Gen (UInt64 × UInt64) := do
  let e ← between 55 2046
  let a := dbl (← coin) e (← bits 52)
  let k ← between 1 (2 ^ 20)
  let b := match ← below 4 with
    | 0 => dbl false (e - 53) 0
    | 1 => dbl false (e - 53) k
    | 2 => dbl false (e - 54) (2 ^ 52 - k)
    | _ => dbl false (e - 52) (2 ^ 51)
  return (a, if ← coin then negW b else b)

/-- Sums just below and above a power of two: `±2^E` with the opposite sign at a quarter of its
ulp, the tie of the binade below, and next to it, and the largest significands of a binade plus
half an ulp and next to it, which round up to the next power of two or stay. -/
def addBinade (_ : Nat) : Gen (UInt64 × UInt64) := do
  let e ← between 56 2045
  let s ← coin
  let k ← between 1 (2 ^ 20)
  let top := dbl s e (2 ^ 52 - 1 - k % 16)
  match ← below 6 with
  | 0 => return (dbl s e 0, dbl (!s) (e - 54) 0)
  | 1 => return (dbl s e 0, dbl (!s) (e - 54) k)
  | 2 => return (dbl s e 0, dbl (!s) (e - 55) (2 ^ 52 - k))
  | 3 => return (top, dbl s (e - 53) 0)
  | 4 => return (top, dbl s (e - 53) k)
  | _ => return (top, dbl s (e - 54) (2 ^ 52 - k))

/-- Sums at the overflow threshold: the largest normals plus half their ulp, next to it, or a
large normal, and pairs of large normals of the same sign. -/
def addOverflow (_ : Nat) : Gen (UInt64 × UInt64) := do
  let s ← coin
  let k ← between 1 (2 ^ 20)
  let a := dbl s 2046 (2 ^ 52 - 1 - k % 16)
  match ← below 5 with
  | 0 => return (a, dbl s 1993 0)
  | 1 => return (a, dbl s 1993 k)
  | 2 => return (a, dbl s 1992 (2 ^ 52 - k))
  | 3 => return (a, dbl (← coin) (← between 1990 2046) (← bits 52))
  | _ => return (dbl s (← between 2040 2046) (← bits 52), dbl s (← between 2040 2046) (← bits 52))

/-- A subnormal of random size, a normal of the smallest binade, one of the largest subnormals,
or a normal of the three smallest binades. -/
def tiny : Gen UInt64 := do
  match ← below 4 with
  | 0 => return dbl (← coin) 0 (← bits (← between 1 52))
  | 1 => return dbl (← coin) 1 (← bits (← between 0 52))
  | 2 => return dbl (← coin) 0 (2 ^ 52 - 1 - (← bits 4))
  | _ => return dbl (← coin) (← between 1 3) (← bits 52)

def addTiny (_ : Nat) : Gen (UInt64 × UInt64) := return (← tiny, ← tiny)

/-- Cancellation: `x` and `-x`; opposite signs with equal exponents and fractions that differ in
random low bits or by up to `2^20` ulps; and a number just above a power of two with one just
below it of the opposite sign. -/
def addCancel (_ : Nat) : Gen (UInt64 × UInt64) := do
  let s ← coin
  let e ← between 1 2046
  let f ← bits 52
  match ← below 4 with
  | 0 => return (dbl s e f, dbl (!s) e f)
  | 1 => return (dbl s e f, dbl (!s) e (f ^^^ (← bits (← between 1 52))))
  | 2 =>
      let e ← between 2 2046
      return (dbl s e (← bits (← between 0 30)),
        dbl (!s) (e - 1) (2 ^ 52 - 1 - (← bits (← between 0 30))))
  | _ => return (dbl s e f, dbl (!s) e ((f + (← between 1 (2 ^ 20))) % 2 ^ 52))

/-- Random normals of either sign whose exponents differ by 0 to 65, the smaller clamped to the
subnormals, in either order. -/
def addAlign (_ : Nat) : Gen (UInt64 × UInt64) := do
  let e ← between 1 2046
  let d ← below 66
  let a := dbl (← coin) e (← bits 52)
  let b := dbl (← coin) (e - min d e) (← bits 52)
  return if ← coin then (a, b) else (b, a)

def randomPair (_ : Nat) : Gen (UInt64 × UInt64) := return (← anyWord, ← anyWord)

/-! ## Products and quotients -/

/-- Exponent fields of two normals whose unbiased exponents sum to `T`. -/
def placeProduct (T : Int) : Gen (Nat × Nat) := do
  let xa ← irange (max (-1022) (T - 1023)) (min 1023 (T + 1022))
  return ((xa + 1023).toNat, (T - xa + 1023).toNat)

/-- Exponent fields of two normals whose unbiased exponents differ by `T`. -/
def placeQuotient (T : Int) : Gen (Nat × Nat) := do
  let xa ← irange (max (-1022) (T - 1022)) (min 1023 (T + 1023))
  return ((xa + 1023).toNat, (xa - T + 1023).toNat)

/-- Normals of random signs with the significands `sa` and `sb` and exponent fields `e`. -/
def withSigs (sa sb : Nat) (e : Nat × Nat) : Gen (UInt64 × UInt64) :=
  return (dbl (← coin) e.1 (sa - 2 ^ 52), dbl (← coin) e.2 (sb - 2 ^ 52))

/-- Significands whose product rounds at a tie: odd parts of `k` and `m` bits whose product has
exactly 54 bits, or `none` when the drawn product has another length. -/
def tieSigs : Gen (Option (Nat × Nat)) := do
  let k ← between 2 52
  let m := if ← coin then 54 - k else 55 - k
  let a ← oddWith k
  let c ← oddWith m
  return if Nat.log2 (a * c) = 53 then some (a * 2 ^ (53 - k), c * 2 ^ (53 - m)) else none

/-- Significands `a` and `b` whose product lies `r` units of its last dropped bit from a tie, for
a nonzero `r` of at most `2^20`: `b ≡ a⁻¹ (2^(t-1) + r)` modulo `2^t`, where `t`, 53 or 52, is
the number of bits that the rounding drops. -/
def nearTieSigs : Gen (Nat × Nat) := do
  for _ in [0:64] do
    let a := 2 ^ 52 + 2 * (← bits 51) + 1
    let r ← small
    if ← coin then
      let b := inv64 a * (2 ^ 52 + r).toNat % 2 ^ 53
      if 2 ^ 52 ≤ b ∧ 2 ^ 105 ≤ a * b then return (a, b)
    else
      let b := inv64 a * (2 ^ 51 + r).toNat % 2 ^ 52 + 2 ^ 52
      if a * b < 2 ^ 105 then return (a, b)
  return (2 ^ 52 + 1, 2 ^ 52 + 1)

/-- Significands `a` and `b` whose quotient lies `r / b` units of `2^-53` or `2^-54` from an
odd multiple of that unit, for a nonzero `r` of at most `2^20`: next to a tie for an odd `r`
and next to a double for an even one.  `a * 2^53 = b * m + r` for a quotient from 1 to 2, and
`a * 2^54 = b * m + r` for one from 1/2 to 1, with `m ≡ -r b⁻¹`. -/
def divSigs : Gen (Nat × Nat) := do
  for _ in [0:64] do
    let b := 2 ^ 52 + 2 * (← bits 51) + 1
    let r ← small
    let n : Nat := if ← coin then 53 else 54
    let m := (-r * Int.ofNat (inv64 b)) % 2 ^ n + (if n = 53 then 2 ^ 53 else 0)
    let v := Int.ofNat b * m + r
    if 2 ^ 53 ≤ m ∧ v % 2 ^ n = 0 then
      let a := (v / 2 ^ n).toNat
      if 2 ^ 52 ≤ a ∧ a < 2 ^ 53 then return (a, b)
  return (2 ^ 52 + 1, 2 ^ 52 + 3)

/-- Odd significands of `k` and `m` bits, `k + m` at most 53, normalized to 53 bits. -/
def shortSigs : Gen (Nat × Nat × Nat) := do
  let k ← between 1 52
  let m ← between 1 (53 - k)
  let a ← oddWith k
  let c ← oddWith m
  return (a, c, m)

def normalProduct : Gen Int := irange (-1022) 1021

def mulTie (_ : Nat) : Gen (UInt64 × UInt64) := do
  for _ in [0:16] do
    match ← tieSigs with
    | some (sa, sb) => return ← withSigs sa sb (← placeProduct (← normalProduct))
    | none => pure ()
  let (sa, sb) ← nearTieSigs
  withSigs sa sb (← placeProduct (← normalProduct))

def mulNearTie (_ : Nat) : Gen (UInt64 × UInt64) := do
  let (sa, sb) ← nearTieSigs
  withSigs sa sb (← placeProduct (← normalProduct))

/-- Products at the overflow threshold: random and near-tie significands with exponents that
sum to 1021 to 1024, and the largest significands times the smallest ones at 1023. -/
def mulOverflow (_ : Nat) : Gen (UInt64 × UInt64) := do
  match ← below 3 with
  | 0 => withSigs (← sig) (← sig) (← placeProduct (← irange 1021 1024))
  | 1 =>
      let (sa, sb) ← nearTieSigs
      withSigs sa sb (← placeProduct (← irange 1021 1024))
  | _ => withSigs (2 ^ 53 - 1 - (← bits 4)) (2 ^ 52 + (← bits 4)) (← placeProduct 1023)

/-- Products in the subnormal range and at the smallest normal: random significands with
exponents that sum to -1080 to -1020; odd parts whose product, below `2^53`, has its lowest bit
at `2^-1075`, a tie of the subnormals; and the largest significands times the smallest ones at
-1023. -/
def mulUnderflow (_ : Nat) : Gen (UInt64 × UInt64) := do
  match ← below 3 with
  | 0 => withSigs (← sig) (← sig) (← placeProduct (← irange (-1080) (-1020)))
  | 1 =>
      let a ← oddWith (← between 1 26)
      let c ← oddWith (← between 1 26)
      let qa ← irange (-1074) (-1)
      return (scaled (← coin) a qa, scaled (← coin) c (-1075 - qa))
  | _ => withSigs (2 ^ 53 - 1 - (← bits 4)) (2 ^ 52 + (← bits 4)) (← placeProduct (-1023))

/-- Exact products: odd parts of at most 53 bits together. -/
def mulExact (_ : Nat) : Gen (UInt64 × UInt64) := do
  let (a, c, m) ← shortSigs
  withSigs (a * 2 ^ (53 - Nat.log2 a - 1)) (c * 2 ^ (53 - m)) (← placeProduct (← normalProduct))

def mulRange (_ : Nat) : Gen (UInt64 × UInt64) := do
  withSigs (← sig) (← sig) (← placeProduct (← irange (-1100) 1030))

def normalQuotient : Gen Int := irange (-1021) 1022

/-- Exact quotients: `a = q * c` over `c` for odd parts `q` and `c` of at most 53 bits
together. -/
def divExact (_ : Nat) : Gen (UInt64 × UInt64) := do
  let (q, c, m) ← shortSigs
  let p := q * c
  withSigs (p * 2 ^ (53 - Nat.log2 p - 1)) (c * 2 ^ (53 - m)) (← placeQuotient (← normalQuotient))

def divNearTie (_ : Nat) : Gen (UInt64 × UInt64) := do
  let (sa, sb) ← divSigs
  withSigs sa sb (← placeQuotient (← normalQuotient))

/-- Quotients at the overflow threshold: random and near-tie significands with exponents that
differ by 1022 to 1024. -/
def divOverflow (_ : Nat) : Gen (UInt64 × UInt64) := do
  let (sa, sb) ← if ← coin then do pure (← sig, ← sig) else divSigs
  withSigs sa sb (← placeQuotient (← irange 1022 1024))

/-- Quotients in the subnormal range: random and near-tie significands with exponents that
differ by -1080 to -1020, and a dividend `t * 2^j + l` units of `2^-1074` over `2^j`, with `l` at
the tie `2^(j-1)`, next to it, or random, or over a small odd divisor, which give ties, near
ties, and zeros of the subnormal grid. -/
def divUnderflow (_ : Nat) : Gen (UInt64 × UInt64) := do
  match ← below 4 with
  | 0 => withSigs (← sig) (← sig) (← placeQuotient (← irange (-1080) (-1020)))
  | 1 =>
      let (sa, sb) ← divSigs
      withSigs sa sb (← placeQuotient (← irange (-1080) (-1020)))
  | 2 =>
      let j ← between 1 52
      let t ← bits (← between 0 (52 - j))
      let h := 2 ^ (j - 1)
      let l ← match ← below 4 with
        | 0 => pure h
        | 1 => pure (h + 1)
        | 2 => pure (h - 1)
        | _ => bits j
      return (scaled (← coin) (t * 2 ^ j + l) (-1074), scaled (← coin) 1 (Int.ofNat j))
  | _ =>
      let n ← bits (← between 1 53)
      return (scaled (← coin) n (-1074), scaled (← coin) (2 * (← bits 3) + 3) (← irange 0 60))

/-! ## Square roots -/

def unary (g : Gen UInt64) (_ : Nat) : Gen (UInt64 × UInt64) := return (← g, 0)

/-- Squares of odd numbers of at most 26 bits times even powers of two, whose roots are
exact. -/
def sqrtExact : Gen UInt64 := do
  let q ← oddWith (← between 1 26)
  let n := q * q
  let j ← between 0 ((2097 - Nat.log2 n) / 2)
  return scaled false n (2 * Int.ofNat j - 1074)

/-- Radicands whose roots lie next to a tie: `4 x' 2^s = M^2 + r` for an odd `M` of 54 bits, a
53-bit significand `x'`, `s` 52 or 53, and `r = 8 t + 7` from `-2^20 + 7` to `2^20 + 7`, so
that `sqrt (x' 2^s)` lies about `r / (4 M)` from the midpoint `M / 2`.  `M` is a root of
`-r` modulo `2^(s+2)`, and the radicand is `x' 2^(s + 2 j)` for a random `j`. -/
def sqrtNearTie : Gen UInt64 := do
  for _ in [0:64] do
    let s : Nat := if ← coin then 52 else 53
    let n := s + 2
    let r : Int := 8 * (← irange (-(2 ^ 17)) (2 ^ 17)) + 7
    let y := sqrtMod ((-r) % 2 ^ n).toNat n
    for M in [y, 2 ^ n - y, (y + 2 ^ (n - 1)) % 2 ^ n, (3 * 2 ^ (n - 1) - y) % 2 ^ n] do
      let v := Int.ofNat (M * M) + r
      if 2 ^ 53 ≤ M ∧ M < 2 ^ 54 ∧ v % 2 ^ n = 0 then
        let x := (v / 2 ^ n).toNat
        if 2 ^ 52 ≤ x ∧ x < 2 ^ 53 then
          let j ← irange (-563) 459
          return dbl false (Int.ofNat s + 2 * j + 1075).toNat (x - 2 ^ 52)
  return 0x3FF0000000000001

def subnormal : Gen UInt64 := do
  match ← below 4 with
  | 0 => return 1
  | 1 => return 0x000FFFFFFFFFFFFF
  | _ => return dbl false 0 ((← bits (← between 1 52)) ||| 1)

/-! ## Conversions -/

def cvtFixed : List Nat :=
  [0, 1, 2, 3, 2 ^ 52 - 1, 2 ^ 52, 2 ^ 52 + 1, 2 ^ 53 - 1, 2 ^ 53, 2 ^ 53 + 1, 2 ^ 53 + 2,
    2 ^ 53 + 3, 2 ^ 54 - 1, 2 ^ 54 + 1, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64 - 2 ^ 10,
    2 ^ 64 - 2 ^ 10 - 1, 2 ^ 64 - 2 ^ 11, 2 ^ 64 - 2 ^ 11 + 2 ^ 10]

/-- The words of `cvtFixed` in turn, and powers of two and their neighbors. -/
def cvtSpecial (i : Nat) : Gen UInt64 := do
  if i % 2 = 0 then return UInt64.ofNat cvtFixed[i / 2 % cvtFixed.length]!
  let k ← between 0 63
  return UInt64.ofNat (2 ^ k + 1 - (← below 3))

/-- Words of 54 to 64 significant bits at a tie: a random 53-bit head and the half of its last
unit. -/
def cvtTie : Gen UInt64 := do
  let L ← between 54 64
  return UInt64.ofNat ((← sig) * 2 ^ (L - 53) + 2 ^ (L - 54))

/-- Words of 55 to 64 bits next to a tie: 1 above or below it, or by up to `2^20` within the
dropped bits. -/
def cvtNearTie : Gen UInt64 := do
  let L ← between 55 64
  let h := 2 ^ (L - 54)
  let d ← if ← coin then pure 1 else between 1 (min (h - 1) (2 ^ 20))
  return UInt64.ofNat ((← sig) * 2 ^ (L - 53) + (if ← coin then h + d else h - d))

/-- Words of 54 to 64 bits whose head is all ones, at a tie or next to one, which round up to the
next power of two or down. -/
def cvtCarry : Gen UInt64 := do
  let L ← between 54 64
  let h := 2 ^ (L - 54)
  let d ← between 0 (h - 1)
  let l ← match ← below 3 with
    | 0 => pure h
    | 1 => pure (h + d)
    | _ => pure (h - d)
  return UInt64.ofNat ((2 ^ 53 - 1) * 2 ^ (L - 53) + l)

/-- Odd numbers of at most 53 bits shifted within the word, which convert exactly. -/
def cvtExact : Gen UInt64 := do
  let k ← between 1 53
  let q ← oddWith k
  return UInt64.ofNat (q * 2 ^ (← between 0 (64 - k)))

/-- Words of 0 to 64 significant bits, the length uniform. -/
def cvtRandom : Gen UInt64 := do
  let L ← between 0 64
  let low ← bits (L - 1)
  return if L = 0 then 0 else UInt64.ofNat (2 ^ (L - 1) + low)

/-! ## Comparisons -/

/-- Equal words. -/
def cmpEqual (_ : Nat) : Gen (UInt64 × UInt64) := do
  let a ← anyWord
  return (a, a)

/-- A word and its negation, a zero of either sign in half of the vectors. -/
def cmpSigns (_ : Nat) : Gen (UInt64 × UInt64) := do
  let neg ← coin
  let w ← anyWord
  let a := if ← coin then dbl neg 0 0 else w
  return (a, negW a)

/-- Neighboring words in either order, which cross a binade, the boundary between subnormals and
normals, or the boundary between the largest normal and infinity at their ends. -/
def cmpAdjacent (_ : Nat) : Gen (UInt64 × UInt64) := do
  let a ← anyWord
  let b := if ← coin then a + 1 else a - 1
  return if ← coin then (a, b) else (b, a)

/-- Words of the same sign and exponent whose fractions differ in random low bits. -/
def cmpClose (_ : Nat) : Gen (UInt64 × UInt64) := do
  let s ← coin
  let e ← below 2048
  let f ← bits 52
  return (dbl s e f, dbl s e (f ^^^ (← bits (← between 1 52))))

/-! ## Classes -/

/-- A class: its name and its vectors by their index in the class. -/
structure Class where
  name : String
  gen : Nat → Gen (UInt64 × UInt64)

def addClasses : List Class :=
  [⟨"special", specialPair⟩, ⟨"tie", addTie⟩, ⟨"binade", addBinade⟩, ⟨"overflow", addOverflow⟩,
    ⟨"tiny", addTiny⟩, ⟨"cancel", addCancel⟩, ⟨"align", addAlign⟩, ⟨"random", randomPair⟩]

def Form.classes : Form → List Class
  | .fadd => addClasses
  | .fsub => addClasses.map fun c => { c with gen := fun i => do
      let (a, b) ← c.gen i
      return (a, negW b) }
  | .fmul =>
      [⟨"special", specialPair⟩, ⟨"tie", mulTie⟩, ⟨"neartie", mulNearTie⟩,
        ⟨"overflow", mulOverflow⟩, ⟨"underflow", mulUnderflow⟩, ⟨"exact", mulExact⟩,
        ⟨"range", mulRange⟩, ⟨"random", randomPair⟩]
  | .fdiv =>
      [⟨"special", specialPair⟩, ⟨"exact", divExact⟩, ⟨"neartie", divNearTie⟩,
        ⟨"overflow", divOverflow⟩, ⟨"underflow", divUnderflow⟩,
        ⟨"range", fun _ => do withSigs (← sig) (← sig) (← placeQuotient (← irange (-1100) 1030))⟩,
        ⟨"random", randomPair⟩]
  | .fsqrt =>
      [⟨"special", fun i => unary (special (i % 26)) i⟩, ⟨"exact", unary sqrtExact⟩,
        ⟨"neartie", unary sqrtNearTie⟩, ⟨"subnormal", unary subnormal⟩,
        ⟨"random", unary anyWord⟩]
  | .ucvtf =>
      [⟨"special", fun i => unary (cvtSpecial i) i⟩, ⟨"tie", unary cvtTie⟩,
        ⟨"neartie", unary cvtNearTie⟩, ⟨"carry", unary cvtCarry⟩, ⟨"exact", unary cvtExact⟩,
        ⟨"random", unary cvtRandom⟩]
  | .fcmp =>
      [⟨"special", specialPair⟩, ⟨"equal", cmpEqual⟩, ⟨"signs", cmpSigns⟩,
        ⟨"adjacent", cmpAdjacent⟩, ⟨"close", cmpClose⟩, ⟨"random", randomPair⟩]

/-- A run of vectors of one form and class. -/
structure Block where
  form : Form
  cls : String
  count : Nat

/-- The operand words of `count` vectors of each form from the seed `seed`, the forms in the
order of `Form.all` and each form's classes in order, two words a vector for a binary form and
one for a unary form, with the blocks in the same order. -/
def vectors (seed : UInt64) (count : Nat) : ByteArray × List Block := Id.run do
  let mut rng : Rng := ⟨seed⟩
  let mut data := ByteArray.emptyWithCapacity (count * 64)
  let mut blocks : Array Block := #[]
  for f in Form.all do
    let cs := f.classes
    let share := count / cs.length
    for (c, j) in cs.zipIdx do
      let n := if j + 1 = cs.length then count - share * (cs.length - 1) else share
      blocks := blocks.push { form := f, cls := c.name, count := n }
      for i in [0:n] do
        let ((a, b), r) := (c.gen i).run rng
        rng := r
        for k in [0:8] do
          data := data.push (byteOf a k)
        if f.binary then
          for k in [0:8] do
            data := data.push (byteOf b k)
  return (data, blocks.toList)

/-! ## The Image -/

/-- The address at which QEMU's virt machine places an arm64 Image whose `text_offset` is 0. -/
def imageBase : UInt64 := 0x40200000

/-- The stores of the eight bytes of register `r` to the UART at X5, lowest first. -/
def emit (r : Fin 32) : List Instr :=
  (List.range 8).flatMap fun k => .strb r 5 0 :: (if k < 7 then [.lsrImm r r 8] else [])

/-- The program at `main`: X5 at the UART, and for each form with `n` vectors a loop of `n`
passes over the vectors from X17, each loading the operands into X2 and X3, running the form's
code, and writing X2 to the UART; then X0 at 0 and `RET` to the exit. -/
def mainCode (main : UInt64) (counts : List (Form × Nat)) : GenM (List Instr) := do
  let mut code := movImm 5 uartAddr
  for (f, n) in counts do
    if n = 0 then continue
    code := code ++ movImm 6 (UInt64.ofNat n)
    let head := after main code.length
    let body := [Instr.ldr 2 17 0] ++ (if f.binary then [Instr.ldr 3 17 1] else []) ++ f.code ++
      emit 2 ++ [.addImm 17 17 (if f.binary then 16 else 8), .subsImm 6 6 1]
    let back ← cbField (after main (code.length + body.length)) head
    code := code ++ body ++ [.bcond 1 back]
  return code ++ [.movz 0 0 0, .ret 30]

/-- The Image of the vectors' words `data` with `counts` vectors of each form, at `imageBase`,
and the offset of the words in the file. -/
def image (data : ByteArray) (counts : List (Form × Nat)) : GenM (ByteArray × Nat) := do
  let base := imageBase + UInt64.ofNat (64 + 4 * startupLength)
  let prog ← mainCode (base + 4) counts
  let vec := roundUp (64 + 4 * (startupLength + 1) + 4 * prog.length) 2048
  let tab := vec + 2048
  let ar := roundUp (tab + 32) 4096
  let clr := ar + data.size
  let areaEnd := roundUp clr 16
  let top := areaEnd + 4096
  unless imageBase.toNat + top ≤ 0x80000000 do
    throw s!"an image of {top} bytes beyond the GiB of RAM"
  let L : Layout :=
    { image := imageBase, base, vectors := imageBase + UInt64.ofNat vec
      table := imageBase + UInt64.ofNat tab, area := imageBase + UInt64.ofNat ar
      clear := imageBase + UInt64.ofNat clr, areaEnd := imageBase + UInt64.ofNat areaEnd
      stackTop := imageBase + UInt64.ofNat top, fileSize := clr, size := top }
  let code := imageBytes ((← startupCode L) ++ prog)
  let head := imageHeader top ++ code ++ List.replicate (vec - 64 - code.length) 0 ++
    vectorBytes ++ tableBytes ++ List.replicate (ar - tab - 32) 0
  return (ByteArray.mk head.toArray ++ data, ar)

/-! ## The check -/

def get64 (b : ByteArray) (o : Nat) : UInt64 :=
  (List.range 8).foldr (fun k acc => (acc <<< 8) ||| b[o + k]!.toUInt64) 0

/-- The position of an exact result on the grid of doubles, the special results, and the order of
a comparison's operands. -/
inductive Tag where
  | exact | tie | nearTie | overflow | subnormal | zero | nan
  | unordered | equal | less | greater
  deriving BEq, Repr

def Tag.all : List Tag :=
  [.exact, .tie, .nearTie, .overflow, .subnormal, .zero, .nan, .unordered, .equal, .less, .greater]

/-- The tags of the form's vectors. -/
def Form.tags : Form → List Tag
  | .fcmp => [.unordered, .equal, .less, .greater]
  | _ => [.exact, .tie, .nearTie, .overflow, .subnormal, .zero, .nan]

def Tag.name : Tag → String
  | .exact => "exact" | .tie => "tie" | .nearTie => "neartie" | .overflow => "overflow"
  | .subnormal => "subnormal" | .zero => "zero" | .nan => "nan" | .unordered => "unordered"
  | .equal => "equal" | .less => "less" | .greater => "greater"

def Tag.index : Tag → Nat
  | .exact => 0 | .tie => 1 | .nearTie => 2 | .overflow => 3 | .subnormal => 4 | .zero => 5
  | .nan => 6 | .unordered => 7 | .equal => 8 | .less => 9 | .greater => 10

/-- The tags of the positive exact result `num / den`, in units of `2^-1074`: exact when it is a
double or zero, a tie when it lies halfway between two doubles, a near tie when it lies within
`2^-10` of a unit in the last place of a tie, and an overflow at or above `2^1024 - 2^970`, from
which nearest rounding gives infinity. -/
def gridTags (num den : Nat) : List Tag :=
  if num = 0 then [.exact]
  else if (2 ^ 54 - 1) * 2 ^ 2044 * den ≤ num then [.overflow]
  else
    let i := num / den
    let d := den * (if i < 2 ^ 53 then 1 else 2 ^ (Nat.log2 i - 52))
    let r := num % d
    let gap := if d ≤ 2 * r then 2 * r - d else d - 2 * r
    if r = 0 then [.exact] else if gap = 0 then [.tie]
    else if gap * 2 ^ 9 ≤ d then [.nearTie] else []

/-- The tags of the form's vector `a`, `b` with the result `w`: those of the exact result when the
operands are finite, and a subnormal result, a zero result of a nonzero exact result, and a NaN
result.  The square root's exact result carries 64 bits below the unit.  A comparison's operands
are unordered, equal, less, or greater, as Talos's `IEEE64.eq` and `IEEE64.lt` give. -/
def tagsOf (f : Form) (a b w : UInt64) : List Tag :=
  open Wasm.IEEE64 in
  if f == .fcmp then
    [if isNaN a || isNaN b then .unordered else if eq a b then .equal else if lt a b then .less
      else .greater]
  else
  let fin := f == .ucvtf || (isFinite a && (!f.binary || isFinite b))
  let exact : Option (Nat × Nat) :=
    if !fin then none
    else match f with
      | .fadd => some ((scaledValue a + scaledValue b).natAbs, 1)
      | .fsub => some ((scaledValue a - scaledValue b).natAbs, 1)
      | .fmul => some (scaledMagnitude a * scaledMagnitude b, 2 ^ 1074)
      | .fdiv =>
          if scaledMagnitude b == 0 then none
          else some (scaledMagnitude a * 2 ^ 1074, scaledMagnitude b)
      | .fsqrt =>
          if sign a && scaledMagnitude a != 0 then none
          else some (Nat.sqrt (scaledMagnitude a * 2 ^ (1074 + 128)), 2 ^ 64)
      | .ucvtf => some (a.toNat * 2 ^ 1074, 1)
      | .fcmp => none
  let grid := match exact with
    | some (n, d) => gridTags n d
    | none => []
  let nonzero := match exact with
    | some (n, _) => n != 0
    | none => false
  grid ++ (if exponent w == 0 && fraction w != 0 then [.subnormal] else []) ++
    (if nonzero && scaledMagnitude w == 0 && !isNaN w then [.zero] else []) ++
    (if isNaN w then [.nan] else [])

/-- A vector whose result differs from the model's. -/
structure Disagreement where
  form : Form
  cls : String
  a : UInt64
  b : UInt64
  got : UInt64
  want : UInt64

/-- A block's outcome: its number of disagreements and its counts of each tag, by `Tag.index`. -/
structure BlockOutcome where
  block : Block
  bad : Nat
  tags : Array Nat

/-- The check of the block `blk`, whose operand words start at `p` in the Image `img` and whose
results start at `q` in the UART's bytes `out`: its outcome and its disagreements. -/
def checkBlock (img out : ByteArray) (blk : Block) (p q : Nat) :
    Except String (BlockOutcome × Array Disagreement) := do
  let stride := if blk.form.binary then 16 else 8
  let mut bad := 0
  let mut tags := Tag.all.toArray.map fun _ => 0
  let mut diffs := #[]
  for i in [0:blk.count] do
    let a := get64 img (p + stride * i)
    let b := if blk.form.binary then get64 img (p + stride * i + 8) else 0
    let got := get64 out (q + 8 * i)
    let want ← match blk.form.model a b with
      | some w => pure w
      | none => throw s!"the model stops on {blk.form.name} of {a}, {b}"
    if got ≠ want then
      bad := bad + 1
      diffs := diffs.push ⟨blk.form, blk.cls, a, b, got, want⟩
    for t in tagsOf blk.form a b want do
      tags := tags.modify t.index (· + 1)
  return ({ block := blk, bad, tags }, diffs)

/-- The check of the UART's bytes `out` against the model for the vectors of the Image `img`,
whose words start at `off`: every result word, and the status byte 0 after the last.  It checks
the blocks in parallel tasks and gives each block's outcome and every disagreement. -/
def checkRun (img out : ByteArray) (off : Nat) (blocks : List Block) :
    Except String (Array BlockOutcome × Array Disagreement) := do
  let total := blocks.foldl (fun n b => n + b.count) 0
  if out.size ≠ 8 * total + 1 then
    throw s!"the UART carries {out.size} bytes, not {8 * total + 1}"
  if out[8 * total]! ≠ 0 then throw s!"the status byte is {out[8 * total]!}, not 0"
  let mut tasks := #[]
  let mut p := off
  let mut q := 0
  for blk in blocks do
    let (p0, q0) := (p, q)
    tasks := tasks.push (Task.spawn fun _ => checkBlock img out blk p0 q0)
    p := p + blk.count * (if blk.form.binary then 16 else 8)
    q := q + 8 * blk.count
  let mut outcomes := #[]
  let mut diffs := #[]
  for t in tasks do
    let (o, d) ← t.get
    outcomes := outcomes.push o
    diffs := diffs ++ d
  return (outcomes, diffs)

end TestSupport.A64.Fp
