import Demos.Avoidance.Program
import Demos.Conjunction.Flat
import Library.Numerics.Interval.Encoding
import Verified.Reflect.Command

/-! The authorizer of `Demos/Avoidance/Program.lean` and the probability enclosure `pcBox` for
interval inputs, compiled by the verified compiler with the interval operations, the library's
`exp`, `erf`, `sin`, and `cos`, and the enclosure of Kepler's equation.  The list puts each
definition after the definitions it calls. -/

namespace Demos.Avoidance

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Trig Demos.Sgp4 in
verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Erf.erfSmall,
  Erf.erfMiddle, Erf.erfTail, Erf.erfExp, Erf.erfWith, absBits, finite, nextUpBits, nextDownBits,
  endpoint, outAdd, outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg,
  extreme, mulEnd, mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt,
  Library.Numerics.Interval.abs, clamp, outward2, kernelSin, kernelCos, remSmall, remMedium, mul64,
  clz64, window, mulTop, shiftTop, remLarge, remPio2, sinWith, cosWith, ofInt, mid, reach,
  lipschitz, sinI, cosI, keplerStep, Kepler.approximate, keplerRootI,
  propagateI, shapeI, planeI, relativeI, afterI, increasing, Demos.Conjunction.sq,
  Demos.Conjunction.expI, Demos.Conjunction.erfI, Demos.Conjunction.gaussI,
  Demos.Conjunction.chordI, Demos.Conjunction.meanI, Demos.Conjunction.erfSumI,
  Demos.Conjunction.panelCore, Demos.Conjunction.nodeRaw, Demos.Conjunction.node,
  Demos.Conjunction.panel, Demos.Conjunction.panels, Demos.Conjunction.setupBox,
  Demos.Conjunction.pcBoxWith, Demos.Conjunction.pcBoxEnds, Demos.Conjunction.pcBox, rd, afterAt,
  assessOne, verdict, allBelow, anyRejected, allFinite, blocksOk, count, valid, triples,
  authorizeWith, authorize]

end Demos.Avoidance
