import Demos.Conjunction.Program
import Library.Numerics.Interval.Functions
import Library.Numerics.Float64.Erfc.Program

/-!
The chi-square distribution in interval arithmetic.  `tailWith` encloses the probability that a
chi-square variable with `k` degrees of freedom exceeds `x`, from its closed form in `exp` and
`erfc`: for `y = x/2`, a sum of `⌊k/2⌋` terms `exp(-y) y^a / Γ(a + 1)`, which a loop computes by
the recurrence `T(a + 1, y) = T(a, y) · x / (2a + 2)`, plus `erfc(√y)` for odd `k`.  `cdfWith` encloses the
distribution function as one less the tail.  `quantileWith` encloses the quantile at `p` by two
bisections of `[0, B]`, with `B = k + 2√(40k) + 80`, that halve the bit patterns of their ends.
`tail`, `cdf`, and `quantile` pass the table of Arm's `exp` and the seven tables of the library's
`erfc`.
-/

namespace Demos.Gate

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-! ### The tail and the distribution function -/

/-- A partial sum of the closed form and its next term. -/
structure Terms where
  acc : Interval
  term : Interval
  deriving Inhabited

/-- `m` steps from `s`: each adds the term to the sum and multiplies the term by `x / (2j + c)`
at step `j`, clamped to `[0, 1]`. -/
def terms (x : Interval) (c m : UInt64) (s : Terms) : Terms :=
  LeanExe.loop m s fun j s =>
    ⟨add s.acc s.term, clamp (div (mul s.term x) (ofInt (j * 2 + c).toInt64)) 0.0 1.0⟩

/-- The image of an interval under `erfc`, which decreases, from the library's values at its
ends. -/
def erfcI (fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (a : Interval) :
    Interval :=
  decreasing a (Erfc.erfcWith fastT accT cexpT asymT asymAccT expAccT excT a.lo)
    (Erfc.erfcWith fastT accT cexpT asymT asymAccT expAccT excT a.hi)

/-- The closed form of the tail at a point `x ≥ 0`, with `y = x/2`: the terms start at `exp(-y)`
for even `k` and at `2 exp(-y) √(y/π)`, after `erfc(√y)`, for odd `k`. -/
def tailCore (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (x : Float) : Interval :=
  let px := point x
  let y := clamp (mul px (point 0.5)) 0.0 x
  let e := clamp (Conjunction.expI expT (neg y)) 0.0 1.0
  if k % 2 == 1 then
    let base := clamp (erfcI fastT accT cexpT asymT asymAccT expAccT excT (sqrt y)) 0.0 1.0
    let t := clamp (mul (mul (point 2.0) e) (sqrt (clamp (div y piI) 0.0 x))) 0.0 1.0
    clamp (terms px 3 (k / 2) ⟨base, t⟩).acc 0.0 1.0
  else clamp (terms px 2 (k / 2) ⟨point 0.0, e⟩).acc 0.0 1.0

/-- An interval that contains the probability that a chi-square variable with `k` degrees of
freedom exceeds `x`, for `k` from 1 to 1,000 and a finite `x`.  Above 1,450, where `exp(-x/2)`
leaves the normal range, it is the interval from 0 to the upper end of the closed form at 1,450,
since the tail decreases. -/
def tailWith (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (x : Float) : Interval :=
  if finite x then
    if 1 ≤ k ∧ k ≤ 1000 then
      if x < 0.0 then point 1.0
      else if x ≤ 1450.0 then tailCore expT fastT accT cexpT asymT asymAccT expAccT excT k x
      else
        let t := tailCore expT fastT accT cexpT asymT asymAccT expAccT excT k 1450.0
        if t.status == 0 then make 0.0 t.hi else rejected
    else rejected
  else rejected

/-- An interval that contains the chi-square distribution function at `x`. -/
def cdfWith (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (x : Float) : Interval :=
  clamp (sub (point 1.0) (tailWith expT fastT accT cexpT asymT asymAccT expAccT excT k x)) 0.0 1.0

/-! ### The quantile -/

/-- The result of the quantile search: status 0 with an interval `[lo, hi]` that contains the
quantile, status 1 for a rejected input, and status 2 when the enclosure at the bracket's upper
end does not show the distribution function at least `p`. -/
structure Quantile where
  status : UInt64
  lo : Float
  hi : Float
  deriving Inhabited

/-- The two ends of a bisection. -/
structure Ends where
  lo : Float
  hi : Float
  deriving Inhabited

/-- The enclosure of the distribution function at a point at or above zero. -/
def cdfAt (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (x : Float) : Interval :=
  if 0.0 ≤ x then cdfWith expT fastT accT cexpT asymT asymAccT expAccT excT k x else rejected

/-- The double whose bit pattern lies halfway between those of the two ends. -/
def split (b : Ends) : Float := Float.ofBits (b.lo.toBits + (b.hi.toBits - b.lo.toBits) / 2)

/-- `h` halvings that move the lower end to the midpoint when the enclosure there lies below `p`,
and the upper end otherwise. -/
def raise (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (p : Float) (h : UInt64) (b : Ends) : Ends :=
  LeanExe.loop h b fun _ b =>
    let m := split b
    let e := cdfAt expT fastT accT cexpT asymT asymAccT expAccT excT k m
    if e.status == 0 && e.hi < p then ⟨m, b.hi⟩ else ⟨b.lo, m⟩

/-- `h` halvings that move the upper end to the midpoint when the enclosure there lies at or
above `p`, and the lower end otherwise. -/
def lower (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (p : Float) (h : UInt64) (b : Ends) : Ends :=
  LeanExe.loop h b fun _ b =>
    let m := split b
    let e := cdfAt expT fastT accT cexpT asymT asymAccT expAccT excT k m
    if e.status == 0 && p ≤ e.lo then ⟨b.lo, m⟩ else ⟨m, b.hi⟩

/-- The upper end of the bracket, `k + 2√(40k) + 80`. -/
def bound (k : UInt64) : Float := k.toFloat + 2.0 * Float.sqrt (40.0 * k.toFloat) + 80.0

/-- An interval that contains the quantile at `p` of the chi-square distribution with `k` degrees
of freedom, from `h` halvings of each bisection. -/
def quantileWith (expT fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64) (k : UInt64)
    (p : Float) (h : UInt64) : Quantile :=
  if finite p then
    if 0.0 < p ∧ p < 1.0 ∧ 1 ≤ k ∧ k ≤ 1000 ∧ h ≤ 64 then
      let b := bound k
      let e := cdfAt expT fastT accT cexpT asymT asymAccT expAccT excT k b
      if e.status == 0 && p ≤ e.lo then
        ⟨0, (raise expT fastT accT cexpT asymT asymAccT expAccT excT k p h ⟨0.0, b⟩).lo, (lower expT fastT accT cexpT asymT asymAccT expAccT excT k p h ⟨0.0, b⟩).hi⟩
      else ⟨2, 0.0, 0.0⟩
    else ⟨1, 0.0, 0.0⟩
  else ⟨1, 0.0, 0.0⟩

def tail (k : UInt64) (x : Float) : Interval :=
  tailWith Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k x

def cdf (k : UInt64) (x : Float) : Interval :=
  cdfWith Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k x

def quantile (k : UInt64) (p : Float) (h : UInt64) : Quantile :=
  quantileWith Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k p h

end Demos.Gate
