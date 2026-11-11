import Demos.Frames.Program
import Verified.Reflect.Command
import Demos.Frames.Flat

namespace Demos.Frames

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd,
  mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, ofInt, ratio, mid, reach, lipschitz, sinI, cosI,
  increasing, Atan.atan, arctanI, gmstSecondsI, turnsI, toEarthI, axisI, cartesianI,
  slopeAI, residualAI, coordsAI, slopeBI, residualBI, coordsBI, lonAI, lonBI, floorOf, angleWith,
  gmstWith, noVec, temeToEcefWith, noCoords, newtonA, newtonB, widen, regimeA, regimeB, longitude,
  toGeodeticWith, toCartesianWith, gmst, temeToEcef, toGeodetic, toCartesian]

end Demos.Frames
