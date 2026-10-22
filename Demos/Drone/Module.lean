import Demos.Drone.Program
import LeanExe.Compiler.Command

namespace Demos.Drone

open Demos.Drone

leanexe_compile drone := [distance, altitude, speed, Library.Numerics.Arithmetic.CeilSqrt.ceilSqrt, restSeconds, edgeTicks,
  choose, predecessor, advance, initial, validHeights, extend, forward, output, compute]

end Demos.Drone
