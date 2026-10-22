import Library.Numerics.Float64.Sinh.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Sinh

verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Tanh.expm1Kernel,
  Tanh.expm1, frexpExp, ldexpExp, sinhWith, coshWith, sinh, cosh]

end Library.Numerics.Float64.Sinh
