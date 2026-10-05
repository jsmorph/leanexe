import LeanExe.Examples.Euler
import Project.Compiler.Command

namespace Project.Euler

open LeanExe.Examples.Euler

leanexe_compile euler := [normalized, energyGuard, side, component, flux, update, advanceCell, initialCell, initialCells,
  sweep, accepted, finishStep, step, scan, tryStep, attempt, advanceWith, advanceStep, runFrom, run, pack,
  solve]

end Project.Euler
