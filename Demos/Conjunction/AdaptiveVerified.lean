import Demos.Conjunction.Adaptive
import Verified.Reflect.Command
import Demos.Conjunction.AdaptiveFlat

namespace Demos.Conjunction.Adaptive

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Demos.Conjunction
  Demos.Conjunction.Accuracy in
verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Erf.erfSmall,
  Erf.erfMiddle, Erf.erfTail, Erf.erfExp, Erf.erfWith, absBits, finite, nextUpBits, nextDownBits,
  endpoint, outAdd, outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg,
  extreme, mulEnd, mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt,
  Library.Numerics.Interval.abs, clamp, outward2, increasing, sq, expI, erfI, setup, gaussI,
  chordI, meanI, erfSumI, panelCore, panel, panelEnd, stepRatio, accept, marchStep, march,
  tolerance, meet, marches, pcAdaptWith, growStep, raiseStep, lowerStep, middle, adaptGrow,
  adaptRaise, adaptLower, adaptSearch, definite, circularErrorAdaptWith, pcAdaptive,
  circularErrorAdaptive]

end Demos.Conjunction.Adaptive
