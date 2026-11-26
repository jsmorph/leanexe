module

public import Library.Numerics.Float64.Erf.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Erf

verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, erfSmall, erfMiddle,
  erfTail, erfExp, erfWith, erf]

end Library.Numerics.Float64.Erf
