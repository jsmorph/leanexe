import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import Library.Numerics.Arithmetic.Uscale.Program

/-! Multiple-precision arithmetic, Algorithms A, S, M, and D of TAOCP §4.3.1, on arrays of digits in
base `b = 2^32`, least significant first, one digit to a word.  A word holds the product of two
digits plus two more digits, since `(b - 1)^2 + 2(b - 1) = b^2 - 1`, which leaves room for the
products and carries of Algorithms M and D.  A read `u[j]!` past the end of `u` gives 0, so the
loops of `add` and `sub` read both arguments up to the larger length.  Each loop's state holds the
word that the next step reads first, the carry or the borrow, before the array that the step
changes. -/

namespace Library.Numerics.MultiPrecision

/-- The larger of the lengths of `u` and `v`. -/
def width (u v : Array UInt64) : UInt64 :=
  if u.size.toUInt64 < v.size.toUInt64 then v.size.toUInt64 else u.size.toUInt64

/-- Algorithm A: the `k + 1` digits of `u + v`, where `k` is the larger length, with the final
carry, 0 or 1, as the last digit. -/
def add (u v : Array UInt64) : Array UInt64 :=
  let s := LeanExe.loop (width u v) ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    ((u[j.toNat]! + v[j.toNat]! + s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + v[j.toNat]! + s.1) % 4294967296))
  s.2.push s.1

/-- Algorithm S without the final borrow: the `k` digits of `u - v + b^k` modulo `b^k`, where `k`
is the larger length, which are the digits of `u - v` when `u ≥ v`.  The step adds the base before
it subtracts, so that no word wraps, and the borrow, 0 or 1, is 1 when the sum stays below the
base.  Knuth's Algorithm S assumes `u ≥ v` and keeps the borrow as 0 or -1. -/
def sub (u v : Array UInt64) : Array UInt64 :=
  (LeanExe.loop (width u v) ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    (1 - (u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) % 4294967296))).2

/-- Algorithm M: the `m + n` digits of `u * v`, where `m` and `n` are the lengths of `u` and `v`.
For each digit `v[j]`, the inner loop adds `u * v[j]` to the digits from position `j` on, and the
last carry becomes digit `j + m`.  The program clears all `m + n` digits at the start, where
Knuth's step M1 clears digits 0 to `m - 1` and each pass writes digit `j + m` before a later pass
reads it.  The program omits Knuth's step M2, which skips a zero digit `v[j]` and leaves the product
unchanged. -/
def mul (u v : Array UInt64) : Array UInt64 :=
  LeanExe.loop v.size.toUInt64
    (LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun _ => (0 : UInt64)) fun j w =>
    let s := LeanExe.loop u.size.toUInt64 ((0 : UInt64), w) fun i s =>
      ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) / 4294967296,
        s.2.set! (i + j).toNat ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) % 4294967296))
    s.2.set! (j + u.size.toUInt64).toNat s.1

/-- The number of significant digits of `v`: one more than the position of its last nonzero
digit, or 0 when every digit is 0. -/
def significant (v : Array UInt64) : UInt64 :=
  LeanExe.loop v.size.toUInt64 (0 : UInt64) fun i t => if v[i.toNat]! = 0 then t else i + 1

/-- Short division of the `len` digits of `x` by the digit `d > 0`, from the most significant digit
down: the `len` digits of the quotient, followed by the remainder. -/
def shortDiv (x : Array UInt64) (d len : UInt64) : Array UInt64 :=
  let s := LeanExe.loop len ((0 : UInt64), LeanExe.build len fun _ => (0 : UInt64)) fun e s =>
    ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) % d,
      s.2.set! (len - 1 - e).toNat ((s.1 * 4294967296 + x[(len - 1 - e).toNat]!) / d))
  s.2.push s.1

/-- The test of step D3: the trial digit `q` is at least the base, or the next digits show it too
large, with `r` the remainder of the trial division, `x` the third digit of the partial remainder,
and `v` the second digit of the divisor. -/
def tooBig (q r x v : UInt64) : Bool :=
  if 4294967296 ≤ q ∨ 4294967296 * r + x < q * v then true else false

/-- Step D3 for the quotient digit at position `j`, where `t ≥ 2` is the number of significant
digits of the normalized divisor `v`: the trial digit from the top digits `w[j + t]` and
`w[j + t - 1]` of the partial remainder `w` and the top digit `v[t - 1]`, decreased while `tooBig`
holds.  It decreases at most twice, since each decrease adds `v[t - 1] ≥ 2^31` to the remainder `r̂`
and the test repeats only while `r̂ < 2^32`, which also keeps `2^32 r̂` below `2^64`. -/
def trial (w v : Array UInt64) (j t : UInt64) : UInt64 :=
  let q0 := (w[(j + t).toNat]! * 4294967296 + w[(j + t - 1).toNat]!) / v[(t - 1).toNat]!
  let r0 := (w[(j + t).toNat]! * 4294967296 + w[(j + t - 1).toNat]!) % v[(t - 1).toNat]!
  let c0 := tooBig q0 r0 w[(j + t - 2).toNat]! v[(t - 2).toNat]!
  let q1 := if c0 then q0 - 1 else q0
  let r1 := if c0 then r0 + v[(t - 1).toNat]! else r0
  if c0 ∧ r1 < 4294967296 ∧ tooBig q1 r1 w[(j + t - 2).toNat]! v[(t - 2).toNat]! then q1 - 1
  else q1

/-- Algorithm D for a dividend `u` of `m` digits and a divisor `v` of `t ≥ 2` significant digits.
Step D1 multiplies both by `d = 2^(32 - L)`, where `L` is the bit length of the divisor's top digit,
so that the top digit of the normalized divisor `vn` is at least `2^31`, and the normalized dividend
has `m + 1` digits.  The main loop's state is the array of `m` quotient digits and the partial
remainder.  Step `e` finds the quotient digit at position `j = m - t - e` by `trial`, subtracts its
product with `vn` from the digits `j` to `j + t` of the partial remainder (step D4), and, when the
difference is negative, decreases the digit and adds `vn` back, dropping the final carry (step D6).
The loop runs `m - t + 1` steps, for `j` from `m - t` down to 0 as in Knuth's loop, and no step when
`t > m`.  The result is the `m` quotient digits followed by `v.size` digits: the low `t` digits of
the partial remainder divided by `d` (step D8), and then zeros. -/
def longDiv (u v : Array UInt64) (t : UInt64) : Array UInt64 :=
  let m := u.size.toUInt64
  let d := (1 : UInt64) <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!)
  let vn := Library.Numerics.Arithmetic.Uscale.mulSmall v d 0
  let s := LeanExe.loop (if t ≤ m then m - t + 1 else 0)
    (LeanExe.build m (fun _ => (0 : UInt64)), Library.Numerics.Arithmetic.Uscale.mulSmall u d 0)
      fun e s =>
      let qh := trial s.2 vn (m - t - e) t
      let ms := LeanExe.loop (t + 1) ((0 : UInt64), (0 : UInt64), s.2) fun i x =>
        ((qh * vn[i.toNat]! + x.1) / 4294967296,
          1 - (x.2.2[(i + (m - t - e)).toNat]! + 4294967296 - (qh * vn[i.toNat]! + x.1) % 4294967296
            - x.2.1) / 4294967296,
          x.2.2.set! (i + (m - t - e)).toNat
            ((x.2.2[(i + (m - t - e)).toNat]! + 4294967296 - (qh * vn[i.toNat]! + x.1) % 4294967296
              - x.2.1) % 4294967296))
      (s.1.set! (m - t - e).toNat (if ms.2.1 = 1 then qh - 1 else qh),
        if ms.2.1 = 1 then
          (LeanExe.loop (t + 1) ((0 : UInt64), ms.2.2) fun i x =>
            ((x.2[(i + (m - t - e)).toNat]! + vn[i.toNat]! + x.1) / 4294967296,
              x.2.set! (i + (m - t - e)).toNat
                ((x.2[(i + (m - t - e)).toNat]! + vn[i.toNat]! + x.1) % 4294967296))).2
        else ms.2.2)
  let r := shortDiv s.2 d t
  LeanExe.build (m + v.size.toUInt64) fun i =>
    if i < m then s.1[i.toNat]! else if i - m < t then r[(i - m).toNat]! else 0

/-- The `m` digits of the quotient of `u` by `v` followed by the `n` digits of the remainder, where
`m` and `n` are the lengths of `u` and `v`.  A divisor of value 0 gives the quotient 0 and the
remainder `u`, cut or padded to `n` digits.  Knuth's Algorithm D requires a divisor of at least two
digits, so a divisor of one significant digit is handled by `shortDiv`, and every other divisor by
`longDiv`. -/
def divide (u v : Array UInt64) : Array UInt64 :=
  if significant v = 0 then
    LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun i =>
      if i < u.size.toUInt64 then 0 else u[(i - u.size.toUInt64).toNat]!
  else if significant v = 1 then
    let r := shortDiv u v[(0 : UInt64).toNat]! u.size.toUInt64
    LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun i =>
      if i ≤ u.size.toUInt64 then r[i.toNat]! else 0
  else longDiv u v (significant v)

end Library.Numerics.MultiPrecision
