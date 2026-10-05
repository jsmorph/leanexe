import LeanExe.Examples.Drone
import Project.Compiler.Command

namespace Project.Drone

open LeanExe.Examples.Drone

leanexe_compile drone := [distance, altitude, speed, ceilSqrt, restSeconds, edgeTicks,
  choose, predecessor, advance, initial, validHeights, extend, forward, output, compute]

end Project.Drone
