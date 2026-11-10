import Demos.Sgp4.Tle
import Verified.Reflect.Command
import Demos.Sgp4.BoxFlat

namespace Demos.Sgp4

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig Pow Spec in
verified_compile boxCompiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd,
  mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, checkint, zeroinfnan, issignaling, powLog, powSpecialCase,
  powExpCore, powExp, powMain, powWith, ofInt, ratio, Library.Numerics.Interval.sq, imax, ifPos, mid, reach, lipschitz, sinI,
  cosI, outward4, cubeEnd, twoThirds, threeHalves, sevenHalves, keplerStep, Kepler.approximate,
  Kepler.rootI, convertI, xkeOfI, periodI, unkozaiI,
  geometryI, atmosphereI, dragCoefI, dragInnerI, dragC4I,
  dragC5I, ratesMeanI, ratesAnglesI, couplingI,
  epochTermsI, higherDI, higherTI, constantsI, secularI,
  dragI, meanI, longPeriodI, anomalyI, shortRadiusI,
  shortAnglesI, orientationI, vectorsI, stateI, elementsI,
  stateAtI, wgs72I, wgs72StateI, initStatus, stateStatus, noBox,
  initBoxWith, propagateBoxWith, sgp4BoxWith, around, sgp4BoxAroundWith, Tle.byteAt, Tle.isDigit,
  Tle.digitOf, Tle.fieldNat, Tle.allDigits, Tle.padded2, Tle.padded3, Tle.checksum, Tle.framed,
  Tle.layout1, Tle.layout2, Tle.sameObject, Tle.pow10, Tle.scaled, Tle.dragTerm, Tle.angle,
  Tle.read, Tle.propagateWith, initBox, propagateBox, sgp4Box, sgp4BoxAround, Tle.propagate]

end Demos.Sgp4
