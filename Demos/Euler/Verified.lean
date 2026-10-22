import Verified.Reflect.Command
import Demos.Euler.Flat

namespace Demos.Euler.Verified

open _root_.Demos.Euler

set_option maxHeartbeats 1000000 in
verified_compile compiled := [normalized, energyGuard, side, component, flux, update,
  advanceCell, initialCell, initialCells, sweep, accepted, finishStep, step, scan, tryStep,
  attempt, advanceWith, advanceStep, runFrom, _root_.Demos.Euler.run, pack, solve,
  Library.Numerics.Bounds.endpoint, Library.Numerics.Bounds.outAdd, Library.Numerics.Bounds.outSub, Library.Numerics.Bounds.outMul, Library.Numerics.Bounds.outDiv, Library.Numerics.Bounds.outSqrt, kineticLower, pressureUpper, soundUpper,
  speedUpper, outwardSide, outwardFlux, faceStep, slope, candidate, tryFactor, limitFactor,
  limit, reconstruct, reconstructedStep, reconstructedSweep, reconstructedFinish,
  reconstructedStepGrid, cellUpper, gridUpper, gridRatio, reconstructedTry,
  reconstructedAttempt, reconstructedAdvanceWith, reconstructedAdvanceStep,
  reconstructedRunFrom, reconstructedRun, reconstructedSolve]

#print axioms compiled.solve.implements
#print axioms compiled.solve.trapFree
#print axioms compiled.reconstructedSolve.implements
#print axioms compiled.reconstructedSolve.trapFree
#print axioms compiled.bytes

end Demos.Euler.Verified
