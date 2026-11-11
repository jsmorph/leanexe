import Demos.Attitude.Program
import Verified.Reflect.Command
import Demos.Attitude.Flat

namespace Demos.Attitude

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig Spec in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd,
  mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, increasing, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop,
  shiftTop, remLarge, remPio2, sinWith, cosWith, ofInt, Library.Numerics.Interval.sq, mid, reach,
  lipschitz, sinI, cosI, Asin.asinRatio, Asin.asin, frameOfI, matrixOfI, boundOfI, triadOfI,
  asinI, widthI, bdOf, etaOf, errOf, boundWith, finishWith, triadWith, triad]

end Demos.Attitude
