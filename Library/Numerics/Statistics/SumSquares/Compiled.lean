module

public import Library.Numerics.Statistics.SumSquares.Program
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compiler's module of `sumSquares`.  The function allocates nothing, so the
generated `compiled.sumSquares.implements` states that function 2 computes `sumSquares` without a
trap. -/

namespace Library.Numerics.Statistics.SumSquares

verified_compile compiled := [sumSquares]

end Library.Numerics.Statistics.SumSquares
