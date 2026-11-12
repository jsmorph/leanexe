import Demos.Gate.GateProgram
import Verified.Reflect.Command
import Demos.Gate.GateFlat

namespace Demos.Gate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval in
verified_compile gateCompiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, fmin, fmax, point, join, add, sub, extreme, mulEnd, mul, divEnd, divCore,
  div, Library.Numerics.Interval.abs, Library.Numerics.Interval.sq, clamp, allFinite, symmetric,
  elimStep, eliminate, gate]

end Demos.Gate
