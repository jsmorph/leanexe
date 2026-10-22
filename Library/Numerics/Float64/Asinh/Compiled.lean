import Library.Numerics.Float64.Asinh.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Asinh

verified_compile compiled := [Log.logNear1, Log.logCore, Log.logWith, Log1p.log1pTail, Log1p.log1p,
  asinhWith, acoshWith, atanh, asinh, acosh]

end Library.Numerics.Float64.Asinh
