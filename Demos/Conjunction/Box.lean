import Demos.Conjunction.Program

/-!
The probability of collision for a mean and a covariance known only within intervals.
`pcBoxWith` is the panel method of `pcWith` with the five scalar inputs replaced by intervals: the
setup computes its quantities from the intervals, and the panels and the constant factor are those
of `pcWith`.  `pcBox` takes the ends of the five intervals and passes the table of Arm's `exp`.
-/

namespace Demos.Conjunction

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The setup of `setup` from intervals of the mean and the covariance. -/
def setupBox (m1 m2 c11 c12 c22 : Interval) (r : Float) : Setup :=
  { m1 := m1
    m2 := m2
    twoC11 := mul (point 2.0) c11
    rho := div c12 c11
    k := mul (sqrt (sub c22 (div (sq c12) c11))) (sqrt (point 2.0))
    r2 := sq (point r) }

/-- An interval that contains the probability of collision for every mean in `m1 × m2` and every
covariance in `c11 × c12 × c22`, for the radius `r`, from `n` panels. -/
def pcBoxWith (tab : Array UInt64) (m1 m2 c11 c12 c22 : Interval) (r : Float) (n : UInt64) :
    Interval :=
  if c11.status == 0 && 0 < c11.lo then
    if 0.0 < r then
      if 1 ≤ n then
        if n ≤ 1048576 then
          let p := mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi c11))))
            (panels tab (setupBox m1 m2 c11 c12 c22 r) r n)
          clamp p 0.0 p.hi
        else rejected
      else rejected
    else rejected
  else rejected

def pcBox (m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r : Float) (n : UInt64) :
    Interval :=
  pcBoxWith Exp.expTable (make m1lo m1hi) (make m2lo m2hi) (make c11lo c11hi) (make c12lo c12hi)
    (make c22lo c22hi) r n

end Demos.Conjunction
