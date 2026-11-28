module

public import Library.Numerics.Float64.Tan.Program
public import Verified.Reflect.Command
public meta import Library.Numerics.Float64.Trig.Program

@[expose] public section

namespace Library.Numerics.Float64.Tan

verified_compile compiled := [Trig.remSmall, Trig.remMedium, Trig.mul64, Trig.clz64, Trig.window,
  Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2, kernelTan, tanWith, tan]

end Library.Numerics.Float64.Tan
