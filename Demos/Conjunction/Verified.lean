import Demos.Conjunction.Message
import Verified.Reflect.Command
import Demos.Conjunction.Flat

namespace Demos.Conjunction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
  Library.Numerics.Arithmetic.Fma in
verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Erf.erfSmall,
  Erf.erfMiddle, Erf.erfTail, Erf.erfExp, Erf.erfWith, msb64, msb128, mul128, shl128, shr128,
  lowBits128, sticky128, bit128, lt128, add128, sub128, roundPack, fmaBits, fma, Erfc.entry,
  Erfc.roundEven, Erfc.floorF, Erfc.toWord, Erfc.sar, Erfc.pow2, Erfc.ldexp, Erfc.fastTwoSum,
  Erfc.twoSum, Erfc.aMul, Erfc.sMul, Erfc.dMul, Erfc.fastSum, Erfc.erfFastTiny, Erfc.erfFastMain,
  Erfc.erfFast, Erfc.mulZ2, Erfc.tinyCoeff, Erfc.erfAccurateTiny, Erfc.erfAccurate, Erfc.q1,
  Erfc.exp1, Erfc.expAccurate, Erfc.asymptIndex, Erfc.erfcAsymptFast, Erfc.erfcFast,
  Erfc.hardCase, Erfc.asymptAccIndex, Erfc.asymptAccurate, Erfc.erfcAsymptAccurate,
  Erfc.erfcAccurate, Erfc.erfcMain, Erfc.erfcWith, absBits, finite, nextUpBits, nextDownBits,
  endpoint, outAdd, outSub, outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg,
  extreme, mulEnd, mul, divEnd, divCore, div, Library.Numerics.Interval.sqrt,
  Library.Numerics.Interval.abs, clamp, outward2, increasing, decreasing, ofInt, sq, expI, erfI,
  erfcI, setup, gaussI, chordI, meanI, erfSumTailI, panelCoreTail, nodeRaw, node, panelTail,
  panelsTail, pcTail, judge, pcTailWith, assessTailWith, pc, assess, rtnAxesI, symMulI,
  bilinearI, rtnToInertialI, planeAxesI, encounterI, encounterAt, setupBox, pcMessageWith,
  assessMessageWith, pcMessage, assessMessage]

end Demos.Conjunction
