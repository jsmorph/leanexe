import Examples.Euler.Steps
import Examples.Euler.ReconstructedLoops
import LeanExe.Encoding.RoundTrip

/-! The encoded bytes of the Euler module decode to a module whose every compiled function, of
both solvers, computes its Lean definition. -/

namespace Examples.Euler

open Wasm LeanExe.Pipeline LeanExe.IR Examples.Euler

/-- `encode` succeeds on `euler.module`, and its bytes decode to `euler.module`. -/
theorem euler_round_trip : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok euler.module :=
  Wasm.Encoding.round_trip euler.module (by decide +kernel) (by decide +kernel)

/-- `encode` succeeds on `euler.module`, and its bytes decode to a module that computes each
function exactly. -/
theorem euler_bytes : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      ImplementsPure m 2 normalizedTuple ∧ ImplementsPure m 3 energyGuardTuple ∧
      ImplementsPure m 4 sideTuple ∧ ImplementsPure m 5 componentTuple ∧
      ImplementsPure m 6 fluxTuple ∧ ImplementsPure m 7 updateTuple ∧
      ImplementsPure m 8 advanceCellTuple ∧ ImplementsPure m 9 initialCellTuple ∧
      Implements m 10 initialCells ∧ Implements m 11 sweepTuple ∧ Implements m 12 accepted ∧
      Implements m 13 finishStepTuple ∧ Implements m 14 stepTuple ∧ Implements m 15 scan ∧
      Implements m 16 tryStepTuple ∧ Implements m 17 attemptTuple ∧
      Implements m 18 advanceWithTuple ∧ Implements m 19 advanceStepTuple ∧
      Implements m 20 runFrom ∧ Implements m 21 Examples.Euler.run ∧
      Implements m 22 packTuple ∧ Implements m 23 solve := by
  obtain ⟨bytes, success, decoded⟩ := euler_round_trip
  exact ⟨bytes, success, euler.module, decoded, normalized_implements, energyGuard_implements,
    side_implements, component_implements, flux_implements, update_implements,
    advanceCell_implements, initialCell_implements, initialCells_implements, sweep_implements,
    accepted_implements, finishStep_implements, step_implements, scan_implements,
    tryStep_implements, attempt_implements, advanceWith_implements, advanceStep_implements,
    runFrom_implements, run_implements, pack_implements, solve_implements⟩

/-- The bytes of `euler.module` decode to a module whose entry 23 computes `solve`: a call with
`n` returns the words of `solve n` or aborts at `unreachable`.  Returned words whose first word is
0 are those of a successful run. -/
theorem euler_solve : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 23 solve ∧
      ∀ n, (solve n)[0]! = 0 → Successful n (solve n) := by
  obtain ⟨bytes, success, m, decoded, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hSolve⟩ := euler_bytes
  exact ⟨bytes, success, m, decoded, hSolve, fun _ h => solve_ok h⟩

/-- `encode` succeeds on `euler.module`, and its bytes decode to a module that computes each
function of the reconstructed solver exactly. -/
theorem euler_reconstructed_bytes : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧
      ImplementsPure m 24 endpointTuple ∧ ImplementsPure m 25 outAddTuple ∧
      ImplementsPure m 26 outSubTuple ∧ ImplementsPure m 27 outMulTuple ∧
      ImplementsPure m 28 outDivTuple ∧ ImplementsPure m 29 outSqrtTuple ∧
      ImplementsPure m 30 kineticLowerTuple ∧ ImplementsPure m 31 pressureUpperTuple ∧
      ImplementsPure m 32 soundUpperTuple ∧ ImplementsPure m 33 speedUpperTuple ∧
      ImplementsPure m 34 outwardSideTuple ∧ ImplementsPure m 35 outwardFluxTuple ∧
      ImplementsPure m 36 faceStepTuple ∧ ImplementsPure m 37 slopeTuple ∧
      ImplementsPure m 38 candidateTuple ∧ ImplementsPure m 39 tryFactorTuple ∧
      ImplementsPure m 40 limitFactorTuple ∧ ImplementsPure m 41 limitTuple ∧
      ImplementsPure m 42 reconstructTuple ∧ ImplementsPure m 43 reconstructedStepTuple ∧
      Implements m 44 reconstructedSweepTuple ∧ Implements m 45 reconstructedFinishTuple ∧
      Implements m 46 reconstructedStepGridTuple ∧ ImplementsPure m 47 cellUpperTuple ∧
      Implements m 48 gridUpper ∧ ImplementsPure m 49 gridRatioTuple ∧
      Implements m 50 reconstructedTryTuple ∧ Implements m 51 reconstructedAttemptTuple ∧
      Implements m 52 reconstructedAdvanceWithTuple ∧
      Implements m 53 reconstructedAdvanceStepTuple ∧ Implements m 54 reconstructedRunFromTuple ∧
      Implements m 55 reconstructedRunTuple ∧ Implements m 56 reconstructedSolveTuple := by
  obtain ⟨bytes, success, decoded⟩ := euler_round_trip
  exact ⟨bytes, success, euler.module, decoded, endpoint_implements, outAdd_implements,
    outSub_implements, outMul_implements, outDiv_implements, outSqrt_implements,
    kineticLower_implements, pressureUpper_implements, soundUpper_implements,
    speedUpper_implements, outwardSide_implements, outwardFlux_implements, faceStep_implements,
    slope_implements, candidate_implements, tryFactor_implements, limitFactor_implements,
    limit_implements, reconstruct_implements, reconstructedStep_implements,
    reconstructedSweep_implements, reconstructedFinish_implements,
    reconstructedStepGrid_implements, cellUpper_implements, gridUpper_implements,
    gridRatio_implements, reconstructedTry_implements, reconstructedAttempt_implements,
    reconstructedAdvanceWith_implements, reconstructedAdvanceStep_implements,
    reconstructedRunFrom_implements, reconstructedRun_implements, reconstructedSolve_implements⟩

/-- The bytes of `euler.module` decode to a module whose entry 56 computes `reconstructedSolve`:
a call with `n` and `trials` returns the words of `reconstructedSolve n trials` or aborts at
`unreachable`.  Returned words whose first word is 0 are those of a successful run. -/
theorem euler_reconstructed_solve : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 56 reconstructedSolveTuple ∧
      ∀ n trials, (reconstructedSolve n trials)[0]! = 0 →
        Successful n (reconstructedSolve n trials) := by
  obtain ⟨bytes, success, m, decoded, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hSolve⟩ := euler_reconstructed_bytes
  exact ⟨bytes, success, m, decoded, hSolve, fun _ _ h => reconstructedSolve_ok h⟩

end Examples.Euler
