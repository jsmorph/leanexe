import Library.Numerics.Float64.Erf.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Erf

verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, erfSmall, erfMiddle,
  erfTail, erfExp, erfWith, erf]

end Library.Numerics.Float64.Erf
