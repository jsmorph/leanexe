import Demos.Euler.ReconstructedProgram
import LeanExe.Compiler.Command

namespace Demos.Euler

open Demos.Euler

leanexe_compile euler := [normalized, energyGuard, side, component, flux, update, advanceCell, initialCell, initialCells,
  sweep, accepted, finishStep, step, scan, tryStep, attempt, advanceWith, advanceStep, runFrom, run, pack,
  solve, Library.Numerics.Bounds.endpoint, Library.Numerics.Bounds.outAdd, Library.Numerics.Bounds.outSub, Library.Numerics.Bounds.outMul, Library.Numerics.Bounds.outDiv, Library.Numerics.Bounds.outSqrt, kineticLower, pressureUpper, soundUpper,
  speedUpper, outwardSide, outwardFlux, faceStep, slope, candidate, tryFactor, limitFactor, limit,
  reconstruct, reconstructedStep, reconstructedSweep, reconstructedFinish, reconstructedStepGrid,
  cellUpper, gridUpper, gridRatio, reconstructedTry, reconstructedAttempt, reconstructedAdvanceWith,
  reconstructedAdvanceStep, reconstructedRunFrom, reconstructedRun, reconstructedSolve]

end Demos.Euler
