import Demos.PassiveSafety.Program
import Verified.Reflect.Command
import Demos.PassiveSafety.Flat

namespace Demos.PassiveSafety

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd,
  mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, ofInt, Library.Numerics.Interval.sq, imax, mid, reach,
  lipschitz, sinI, cosI, flowPositionI, flowVelocityI, sepSquareI, rcSquareI, sepTaylorI,
  rcTaylorI, box, runs, panelEnd, nonneg, record, accepts, march, positionI, velocityI, straddles,
  meet, midpoint, xzBound, smoothRc, smoothSep, sepPanel, sepStep, sepSearch, lastTime, rcPanel,
  rcStep, rcSearch, searchStatus, scanStep, finiteAll, valuesOk, square, sqrtDown, checkWith,
  check]

end Demos.PassiveSafety
