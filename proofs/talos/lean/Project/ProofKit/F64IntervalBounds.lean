import Project.ProofKit.F64IntervalComposition
import Project.ProofKit.RealBalanceEnclosure

namespace Project.ProofKit.F64Interval
open CodeLib.IEEE64

theorem Sound.absolute_bound {a : Bounds} {x : ℝ} (h : Sound a x) :
    |x| ≤ max (-value a.lower) (value a.upper) :=
  RealBalanceEnclosure.absolute_bound _ _ _ h.2.2.2

theorem Valid.absolute_bound {a : Bounds} {x : ℝ}
    (h : Valid a x) (ha : a.status = 0) :
    |x| ≤ max (-value a.lower) (value a.upper) := (h ha).absolute_bound

#print axioms Sound.absolute_bound
#print axioms Valid.absolute_bound
end Project.ProofKit.F64Interval
