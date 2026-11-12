import Demos.Attitude.QProgram
import Verified.Reflect.Command
import Demos.Attitude.QFlat

/-! The q-method of `Demos/Attitude/QProgram.lean`, compiled by the verified compiler with the
interval operations and the library's `sin`, `cos`, and `asin`.  The list puts each definition
after the definitions it calls. -/

namespace Demos.Attitude.QMethod

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd,
  mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp,
  outward2, increasing, kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop,
  shiftTop, remLarge, remPio2, sinWith, cosWith, ofInt, mid, reach, lipschitz, sinI, cosI,
  Asin.asinRatio, Asin.asin, Demos.Attitude.asinI, rd, isWhole, allFinite, recordOk, valid,
  Spec.obsScaleI, Spec.obsFirstI, Spec.obsRestI, Spec.obsTrueI, addObs, zeroI, accumulate,
  accepted, rotCS, mixL, mixR, rot01, rot02, rot03, rot12, rot13, rot23, sweep, jacobi, top4, pick,
  column, normalize, shiftI, mag, swap4, swap3, swap2, Spec.schur4I, Spec.schur3I, Spec.schur2I,
  stage4, stage3, stage2, pivotsI, isPos, isNeg, signsOk, rejectWith, Spec.applyKI,
  Spec.residOfI, Spec.boundsOfI, certify, qmethodWith, qmethod]

end Demos.Attitude.QMethod
