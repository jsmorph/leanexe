import Demos.Orbit.GibbsBox
import Verified.Reflect.Command
import Demos.Orbit.Flat

namespace Demos.Orbit

set_option maxHeartbeats 0 in
open Library.Numerics.Bounds Library.Numerics.Interval in
verified_compile gibbsCompiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd,
  outSub, outMul, outDiv, outSqrt, fmin, fmax, make, join, add, sub, extreme, mulEnd, mul,
  divEnd, divCore, div, Library.Numerics.Interval.sqrt, Library.Numerics.Interval.abs,
  Library.Numerics.Interval.sq, sqrI, lengthOfI, crossOfI, weightedI, gibbsCoordsI, tripleI,
  noVelocity, noTable, valid, gibbsBox, gibbsBounds]

end Demos.Orbit
