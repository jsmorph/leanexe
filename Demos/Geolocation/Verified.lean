import Demos.Geolocation.Flat
import Verified.Reflect.Command

/-! The geolocation program of `Demos/Geolocation/Program.lean`, compiled by the verified compiler
with the interval operations, the library's `sin` and `cos`, and the frames demo's sidereal
angle, rotation into the Earth-fixed frame, and enclosure of the WGS 84 position.  The list puts
each definition after the definitions it calls. -/

namespace Demos.Geolocation

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig
  Demos.Screening in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd, outSub,
  outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd, mul,
  divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, ofInt, ratio, mid, reach, lipschitz, sinI, cosI,
  Demos.Frames.gmstSecondsI, Demos.Frames.turnsI, Demos.Frames.toEarthI,
  Demos.Frames.cartesianI, Demos.Frames.floorOf, Demos.Frames.angleWith, distI, rateI, tdoaResI,
  fdoaResI, spinI, earthVelI, rd, middle, allFinite, isWhole, pair, stateOf, component,
  receivers, allAccepted, residual, verdictStep, boxTest, parallel, longest, sideLo, sideHi,
  lowerHalf, upperHalf, splits, boxStep, refine, fresh, level, search, finalStep, finalBoxes,
  ordered, receiverOk, measurementOk, entriesOk, valid, sevens, outputOf, regionOf, locateWith,
  locate]

end Demos.Geolocation
