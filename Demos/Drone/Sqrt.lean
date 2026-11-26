module

public import Library.Numerics.Arithmetic.CeilSqrt.Proof
public import Demos.Drone.Program

@[expose] public section

namespace Demos.Drone

export Library.Numerics.Arithmetic.CeilSqrt (sqrtStep ceilSqrt_loop)

namespace Sqrt
export Library.Numerics.Arithmetic.CeilSqrt.Sqrt (Bracket bracket_step ceilSqrt_correct)
end Sqrt

end Demos.Drone
