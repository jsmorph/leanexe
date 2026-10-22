import Library.Numerics.Float64.Trig.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Trig

verified_compile compiled := [kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window,
  mulTop, shiftTop, remLarge, remPio2, sinWith, cosWith, sin, cos]

end Library.Numerics.Float64.Trig
