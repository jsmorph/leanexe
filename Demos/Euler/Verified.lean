import Verified.Reflect.Command
import Demos.Euler.Flat
import Demos.Euler.Buffered

/-! The verified compilation of the Euler solvers.  The exports `solve` and `reconstructedSolve` are
the buffered solvers of `Demos.Euler.Buffered`, which equal `Demos.Euler.solve` and
`Demos.Euler.reconstructedSolve` by `Demos.Euler.Buffered.solve_eq` and `reconstructedSolve_eq`.
The module also compiles the sweeps, tries, and timesteps of both programs that build a new grid
for each sweep, which the module cases call. -/

namespace Demos.Euler.Verified

open _root_.Demos.Euler

set_option verified_compile.alignedNative true in
set_option maxHeartbeats 1000000 in
verified_compile compiled := [normalized, energyGuard, side, component, flux, update,
  advanceCell, initialCell, initialCells, sweep, accepted, finishStep, step, scan, tryStep,
  attempt, advanceWith, advanceStep, pack, Buffered.sweepInto, Buffered.tryInto,
  Buffered.attemptInto, Buffered.advanceInto, Buffered.stepInto, Buffered.runFromInto,
  Buffered.runInto, Buffered.solve,
  Library.Numerics.Bounds.endpoint, Library.Numerics.Bounds.outAdd, Library.Numerics.Bounds.outSub, Library.Numerics.Bounds.outMul, Library.Numerics.Bounds.outDiv, Library.Numerics.Bounds.outSqrt, kineticLower, pressureUpper, soundUpper,
  speedUpper, outwardSide, outwardFlux, faceStep, slope, candidate, tryFactor, limitFactor,
  limit, reconstruct, reconstructedStep, reconstructedSweep, reconstructedFinish,
  reconstructedStepGrid, cellUpper, gridUpper, gridRatio, reconstructedTry,
  reconstructedAttempt, reconstructedAdvanceWith, reconstructedAdvanceStep,
  Buffered.reconstructedSweepInto, Buffered.reconstructedTryInto,
  Buffered.reconstructedAttemptInto, Buffered.reconstructedAdvanceInto,
  Buffered.reconstructedStepInto, Buffered.reconstructedRunFromInto,
  Buffered.reconstructedRunInto, Buffered.reconstructedSolve]

#print axioms compiled.solve.implements
#print axioms compiled.solve.trapFree
#print axioms compiled.reconstructedSolve.implements
#print axioms compiled.reconstructedSolve.trapFree
#print axioms compiled.bytes

end Demos.Euler.Verified
