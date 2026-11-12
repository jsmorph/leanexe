import Demos.Events.Flat
import Verified.Reflect.Command

/-! The event-window program of `Demos/Events/Program.lean`, compiled by the verified compiler
with the interval operations, the library's `sin` and `cos`, the enclosure of Kepler's equation,
and the screening program's positions.  The list puts each definition after the definitions it
calls. -/

namespace Demos.Events

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig Demos.Sgp4
  Demos.Screening in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd, outSub,
  outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd, mul,
  divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop,
  remLarge, remPio2, sinWith, cosWith, ofInt, ratio, mid, reach, lipschitz, sinI, cosI, keplerStep,
  Kepler.approximate, keplerI, Demos.Screening.Spec.orbitI, Demos.Screening.Spec.pathPointI,
  Demos.Screening.Spec.anomalyI, rd, object, pointAt, positionAt, middle, Spec.sunDirI,
  Spec.angleI, Spec.lengthI, Spec.shadowPartsI, Spec.vectorPartI, Spec.rswVecI, Spec.ratesI,
  Spec.padI, partsAt, cellTest, refineCells, isolateLevel, isolate, finalRuns, joinStep, joinRuns,
  triples, isWhole, allFinite, eventOk, valid, setup, outputOf, eventsWith, events]

end Demos.Events
