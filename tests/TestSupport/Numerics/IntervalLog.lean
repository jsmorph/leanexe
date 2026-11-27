module

public import Library.Numerics.Interval.FunctionsProof
public meta import Library.Numerics.Interval.Functions

@[expose] public section

/-!
Tests of `Library.Numerics.Interval.logI` and `Library.Numerics.Interval.encloses_logI`.  At the
point 2, `logI` returns the doubles two steps on each side of `0x3FE62E42FEFA39EF`, the double
nearest `log 2`, and it rejects an interval that reaches zero.  `log_ratio` encloses the logarithm
of a ratio of integers, the form of a program that takes the logarithm of a quantity that it
computes on intervals.
-/

namespace TestSupport.Numerics.IntervalLog

open Library.Numerics.Interval Library.Numerics.Float64

#guard (logI Log.logTable Log.logTable2 (point 2.0)).status == 0
#guard (logI Log.logTable Log.logTable2 (point 2.0)).lo.toBits == 0x3FE62E42FEFA39ED
#guard (logI Log.logTable Log.logTable2 (point 2.0)).hi.toBits == 0x3FE62E42FEFA39F1
#guard (logI Log.logTable Log.logTable2 (point 0.0)).status != 0
#guard (logI Log.logTable Log.logTable2 ⟨0, -1.0, 2.0⟩).status != 0

/-- `logI` of the interval of `n / d` contains `log (n / d)`. -/
theorem log_ratio {n d : Int64} (hn : n.toInt.natAbs ≤ 2 ^ 53) (hd : d.toInt.natAbs ≤ 2 ^ 53) :
    Encloses (logI Log.logTable Log.logTable2 (ratio n d))
      (Real.log ((n.toInt : ℝ) / (d.toInt : ℝ))) :=
  encloses_logI (encloses_ratio hn hd rfl)

#print axioms encloses_logI
#print axioms log_ratio

end TestSupport.Numerics.IntervalLog
