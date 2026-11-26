module

public import Library.Numerics.Float64.Asinh.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Asinh

verified_compile compiled := [Log.logNear1, Log.logCore, Log.logWith, Log1p.log1pTail, Log1p.log1p,
  asinhWith, acoshWith, atanh, asinh, acosh]

end Library.Numerics.Float64.Asinh
