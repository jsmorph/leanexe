module

public import Demos.Orbit.LambertBox
public import Verified.Reflect.Command
public import Demos.Orbit.LambertFlat
public meta import Library.Numerics.Float64.Log.Program

@[expose] public section

namespace Demos.Orbit

set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 Asin Log in
verified_compile lambertCompiled := [asinRatio, acos, logNear1, logCore, logWith, absBits, finite,
  nextUpBits, nextDownBits, endpoint, outAdd, outSub, outMul, outDiv, outSqrt, fmin, fmax, make,
  point, join, add, sub, neg, extreme, mulEnd, mul, divEnd, divCore, div,
  Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs, clamp, outward2, increasing,
  decreasing, ofInt, ratio, Library.Numerics.Interval.sq, imax, sqrI, lengthOfI, crossOfI,
  directionI, geometryI, componentsI, velocitiesI, oneI, acosI, logI, arcoshI, tofI, above,
  below, midpoint, raiseStep, lowerStep, bracket, raise, lower, noTable, valid, noTransfer, startLow,
  signOf, solve, lambertBoxWith, lambertBox, lambertBoundsWith, lambertBounds]

end Demos.Orbit
