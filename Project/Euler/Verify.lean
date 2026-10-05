import Project.Euler.Steps
import Project.Encoding.RoundTrip

/-! The encoded bytes of the first-order Euler module decode to a module whose every compiled
function computes its Lean definition. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR LeanExe.Examples.Euler

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
      Implements m 20 runFrom ∧ Implements m 21 LeanExe.Examples.Euler.run ∧
      Implements m 22 packTuple ∧ Implements m 23 solve := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip euler.module (by decide +kernel) (by decide +kernel)
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

end Project.Euler
