import Examples.Euler.ReconstructedProgram
import Project.Compiler.Command

namespace Examples.Euler

open Examples.Euler

leanexe_compile euler := [normalized, energyGuard, side, component, flux, update, advanceCell, initialCell, initialCells,
  sweep, accepted, finishStep, step, scan, tryStep, attempt, advanceWith, advanceStep, runFrom, run, pack,
  solve, endpoint, outAdd, outSub, outMul, outDiv, outSqrt, kineticLower, pressureUpper, soundUpper,
  speedUpper, outwardSide, outwardFlux, faceStep, slope, candidate, tryFactor, limitFactor, limit,
  reconstruct, reconstructedStep, reconstructedSweep, reconstructedFinish, reconstructedStepGrid,
  cellUpper, gridUpper, gridRatio, reconstructedTry, reconstructedAttempt, reconstructedAdvanceWith,
  reconstructedAdvanceStep, reconstructedRunFrom, reconstructedRun, reconstructedSolve]

end Examples.Euler
