import Library.Numerics.Float64.Sinpi.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Sinpi

verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Tan.kernelTan, toSingle, piProduct,
  kernelSinpi, kernelCospi, kernelTanpi, piTiny, ffloor, oddPart, sinpi, cospi, tanpi]

end Library.Numerics.Float64.Sinpi
