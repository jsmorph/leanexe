module

public import Library.Numerics.Interval.Program
public import Verified.Reflect.Command
public import Library.Numerics.Interval.Encoding

@[expose] public section

namespace Library.Numerics.Interval

open Library.Numerics.Bounds in
verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd, outSub,
  outMul, outDiv, outSqrt, fmin, fmax, make, point, join, add, sub, neg, extreme, mulEnd, mul,
  divEnd, divCore, div, sqrt, abs, clamp, outward2, increasing, decreasing]

end Library.Numerics.Interval
