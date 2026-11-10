import Demos.Conjunction.Program
import Verified.Reflect.Command
import Demos.Conjunction.Flat

namespace Demos.Conjunction

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 in
verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Erf.erfSmall,
  Erf.erfMiddle, Erf.erfTail, Erf.erfExp, Erf.erfWith, absBits, finite, nextUpBits, nextDownBits,
  endpoint, outAdd, outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg,
  extreme, mulEnd, mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt,
  Library.Numerics.Interval.abs, clamp, outward2, increasing, sq, expI,
  erfI, setup, gaussI, chordI, meanI, erfSumI, panelCore, nodeRaw, node, panel, panels, pcWith, assessWith, pc, assess]

end Demos.Conjunction
