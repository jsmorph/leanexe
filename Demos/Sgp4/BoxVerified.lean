import Demos.Sgp4.Box
import Verified.Reflect.Command
import Demos.Sgp4.BoxFlat

namespace Demos.Sgp4

set_option maxRecDepth 100000 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig Pow Spec in
verified_compile boxCompiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd,
  mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, checkint, zeroinfnan, issignaling, powLog, powSpecialCase,
  powExpCore, powExp, powMain, powWith, ofInt, ratio, sq, imax, ifPos, mid, reach, lipschitz, sinI,
  cosI, outward4, cubeEnd, twoThirds, threeHalves, sevenHalves, keplerStep, Kepler.approximate,
  Kepler.root.interval, convert.interval, xkeOf.interval, period.interval, unkozai.interval,
  geometry.interval, atmosphere.interval, dragCoef.interval, dragInner.interval, dragC4.interval,
  dragC5.interval, ratesMean.interval, ratesAngles.interval, coupling.interval,
  epochTerms.interval, higherD.interval, higherT.interval, constants.interval, secular.interval,
  drag.interval, mean.interval, longPeriod.interval, anomaly.interval, shortRadius.interval,
  shortAngles.interval, orientation.interval, vectors.interval, state.interval, elements.interval,
  stateAt.interval, wgs72.interval, wgs72State.interval, initStatus, stateStatus, noBox,
  initBoxWith, propagateBoxWith, sgp4BoxWith, around, sgp4BoxAroundWith, initBox, propagateBox,
  sgp4Box, sgp4BoxAround]

end Demos.Sgp4
