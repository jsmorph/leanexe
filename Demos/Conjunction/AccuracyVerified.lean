module

public import Demos.Conjunction.Accuracy
public import Verified.Reflect.Command
public import Demos.Conjunction.AccuracyFlat
public meta import Library.Numerics.Float64.Exp.Program

@[expose] public section

namespace Demos.Conjunction.Accuracy

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Demos.Conjunction in
verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Erf.erfSmall,
  Erf.erfMiddle, Erf.erfTail, Erf.erfExp, Erf.erfWith, absBits, finite, nextUpBits, nextDownBits,
  endpoint, outAdd, outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg,
  extreme, mulEnd, mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt,
  Library.Numerics.Interval.abs, clamp, outward2, increasing, sq, expI, erfI, setup, gaussI,
  chordI, meanI, erfSumI, panelCore, nodeRaw, node, panel, panels, pcWith, growStep, raiseStep,
  lowerStep, middle, diskGrow, diskRaise, diskLower, diskSearch, definite, circularErrorWith,
  lineScale, lineAt, lineGrow, lineRaise, lineLower, lineSearch, linearErrorWith, circularError,
  linearError]

end Demos.Conjunction.Accuracy
