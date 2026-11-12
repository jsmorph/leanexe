import Demos.Screening.Flat
import Verified.Reflect.Command

/-! The screening program of `Demos/Screening/Program.lean`, compiled by the verified compiler with
the interval operations, the library's `sin` and `cos`, and the enclosure of Kepler's equation.
The list puts each definition after the definitions it calls. -/

namespace Demos.Screening

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig Demos.Sgp4
  Spec in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd, outSub,
  outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd, mul,
  divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, ofInt, mid, reach, lipschitz, sinI, cosI, keplerStep,
  Kepler.approximate, keplerI, orbitI, pathPointI, anomalyI, distSqI, rd, object, pointAt,
  positionAt, gapSq, middle, apsidesExclude, cellExclude, cellClose, anyClose, refineCells,
  pathLevel, pathFilter, spanTest, refineSpans, isolateLevel, isolate, finalSpans, mergeStep,
  merge, triples, isWhole, orbitOk, allFinite, valid, objectAt, isolationOutput, screenWith, screen]

end Demos.Screening
