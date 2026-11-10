import Demos.Sgp4.Program
import Verified.Reflect.Command
import Demos.Sgp4.Flat

namespace Demos.Sgp4

set_option maxRecDepth 100000 in
open Library.Numerics.Float64 Trig Pow Atan in
verified_compile compiled := [kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window,
  mulTop, shiftTop, remLarge, remPio2, sinWith, cosWith, checkint, zeroinfnan, issignaling,
  powLog, powSpecialCase, powExpCore, powExp, powMain, powWith, atan, atan2, isFinite, failed,
  initCore, initWith, stopped, keplerStep, propagateWith, sgp4With, init, propagate, sgp4]

end Demos.Sgp4
