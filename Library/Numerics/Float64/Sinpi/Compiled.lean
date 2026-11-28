module

public import Library.Numerics.Float64.Sinpi.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Sinpi

verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Tan.kernelTan, toSingle, piProduct,
  kernelSinpi, kernelCospi, kernelTanpi, piTiny, ffloor, oddPart, sinpi, cospi, tanpi]

end Library.Numerics.Float64.Sinpi
