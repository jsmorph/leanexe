import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import Library.Numerics.Arithmetic.Uscale.Program

/-! Multiple-precision arithmetic, Algorithms A, S, M, and D of TAOCP §4.3.1, on arrays of digits in
base `2^32`, least significant first.  A read `u[j]!` past the end of `u` gives 0, so the loops
read both arguments up to the larger length.  Each loop's state holds the word that the next step
reads first, the carry or the borrow, before the array that the step changes. -/

namespace Library.Numerics.MultiPrecision

/-- The larger of the lengths of `u` and `v`. -/
def width (u v : Array UInt64) : UInt64 :=
  if u.size.toUInt64 < v.size.toUInt64 then v.size.toUInt64 else u.size.toUInt64

/-- Algorithm A: the digits of `u + v`, with the final carry as the last digit. -/
def add (u v : Array UInt64) : Array UInt64 :=
  let s := LeanExe.loop (width u v) ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    ((u[j.toNat]! + v[j.toNat]! + s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + v[j.toNat]! + s.1) % 4294967296))
  s.2.push s.1

/-- Algorithm S: the digits of `u - v`, without the final borrow.  The step adds the base before
it subtracts, so that no word wraps, and the borrow is 1 when the sum stays below the base. -/
def sub (u v : Array UInt64) : Array UInt64 :=
  (LeanExe.loop (width u v) ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    (1 - (u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) % 4294967296))).2

/-- Algorithm M: the digits of `u * v`.  For each digit `v[j]`, the inner loop adds `u * v[j]` to
the digits from position `j` on, and the last carry becomes digit `j + m`. -/
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

/-- Step D3: the trial quotient digit from the top digits `w[j + t]` and `w[j + t - 1]` of the
partial remainder and the top digit `v[t - 1]` of the normalized divisor, decreased while `tooBig`
holds.  It decreases at most twice, since each decrease adds `v[t - 1] ≥ 2^31` to the remainder
`r̂` and the test repeats only while `r̂ < 2^32`. -/
def trial (w v : Array UInt64) (j t : UInt64) : UInt64 :=
  let q0 := (w[(j + t).toNat]! * 4294967296 + w[(j + t - 1).toNat]!) / v[(t - 1).toNat]!
  let r0 := (w[(j + t).toNat]! * 4294967296 + w[(j + t - 1).toNat]!) % v[(t - 1).toNat]!
  let c0 := tooBig q0 r0 w[(j + t - 2).toNat]! v[(t - 2).toNat]!
  let q1 := if c0 then q0 - 1 else q0
  let r1 := if c0 then r0 + v[(t - 1).toNat]! else r0
  if c0 ∧ r1 < 4294967296 ∧ tooBig q1 r1 w[(j + t - 2).toNat]! v[(t - 2).toNat]! then q1 - 1
  else q1

/-- Algorithm D for a divisor of `t ≥ 2` significant digits.  Step D1 multiplies both arguments by
`d = 2^(32 - L)`, where `L` is the bit length of the divisor's top digit, so that the top digit of
the normalized divisor `vn` is at least `2^31`.  Each step of the main loop finds the quotient digit
at position `j = m - t - e` by `trial`, subtracts its product with `vn` from the digits `j` to `j + t`
of the partial remainder (step D4), and adds `vn` back and decreases the digit when the difference
is negative (step D6).  The remainder is the low `t` digits of the partial remainder divided by `d`
(step D8). -/
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

/-- The digits of the quotient of `u` by `v`, followed by those of the remainder. -/
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
