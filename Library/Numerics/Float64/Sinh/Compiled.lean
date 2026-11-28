module

public import Library.Numerics.Float64.Sinh.Program
public import Verified.Reflect.Command
public meta import Library.Numerics.Float64.Exp.Program

@[expose] public section

namespace Library.Numerics.Float64.Sinh

verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Tanh.expm1Kernel,
  Tanh.expm1, frexpExp, ldexpExp, sinhWith, coshWith, sinh, cosh]

end Library.Numerics.Float64.Sinh
