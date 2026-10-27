import Verified.Reflect.Command
import Demos.Slew.Flat

/-! The slew planner of `Demos/Slew/Program.lean`, compiled unchanged by the verified compiler.
The list puts each definition after the definitions it calls: the library's `atan` and `atan2`,
the quaternion helpers, input validation, the static and edge checks, the cost, the search, and
the output.  `dot`, `cross`, `rd`, `v3At`, `q4At`, `isWord`, `unitV`, and `unitQ` are `@[inline]`
and unfold at their uses; the constants `margin`, `eta`, `sMin`, `tolNorm`, `rateMin`, `accelMin`,
`axisMin`, `maxFinite`, and `infinity` are reflected as their values.  The compiler's theorem
`compiled.plan.implements` states that the module's `plan` export computes `Demos.Slew.plan`, or
traps at `unreachable`, which an allocation permits when memory runs out. -/

namespace Demos.Slew.Verified

open _root_.Demos.Slew
open _root_.Library.Numerics.Float64.Atan

verified_compile compiled := [atan, atan2, qrot, relative, nodeAt, dims, allFinite, bodiesOk,
  conesOk, waysOk, validInput, attitudeOk, edgeOk, angleOf, ceilMs, slewTicks, selectNext, relax,
  round, initial, search, pathLength, pathNode, segmentField, statusOnly, output, plan]

end Demos.Slew.Verified
