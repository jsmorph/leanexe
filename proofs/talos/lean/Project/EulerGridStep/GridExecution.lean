import Project.EulerGridStep.GridValidBody
import Project.EulerGridStep.GridEntryReady

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- The complete exported function on valid entry guards, including every numerical rejection. -/
theorem step_valid_entry_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer allocs releases frees : UInt64)
    (base : Nat) (input : Array UInt64)
    (hReady : GridEntryReady initial pointer input base allocs releases frees)
    (hValid : gridEntryInvalid ratio input.size = false) :
    TerminatesWith env m 36 initial [.i64 pointer, .i64 ratio]
      (fun final values => ∃ root, values = [.i64 root] ∧ UInt64Array.At final root (Model.stepCheckedBits ratio input)) := by
  refine TerminatesWith.of_wp_entry_for (f := func36Def)
    (by simpa [layout.noImports] using layout.step) ?_ (by simp [layout.noImports])
  change wp m func36 _ initial (gridEntryFrame ratio pointer) env
  rw [grid_function_shape]
  apply grid_entry_guards_spec layout env initial ratio pointer input hReady.inputAt
  have hGuard : gridGuardFrame ratio pointer input.size =
      { gridGuardFrame ratio pointer input.size with values := [.i32 0] } := by
    simp [gridGuardFrame, hValid]
  rw [hGuard]
  change wp m [.iff 0 0 gridInvalidBody gridValidBody, .localGet 32] _ initial
    { gridGuardFrame ratio pointer input.size with values := [.i32 0] } env
  apply wp_iff_cons rfl
  rw [ite_eq_right (by decide : ¬ (0 : UInt32) ≠ 0)]
  change wp m (gridValidBody ++ []) _ initial (gridValidEntryFrame ratio pointer input.size) env
  apply grid_valid_body_spec layout env initial ratio pointer allocs releases frees base input
    (Model.stepCheckedBits ratio input) hReady.inputAt (grid_valid_cells ratio input hValid)
    hReady.pages hReady.budget hReady.heap hReady.freeHead hReady.allocations hReady.releases hReady.frees
    hReady.separate (grid_model_valid ratio input hValid) _ []
  intro final index output scratch hOutput hArray
  rw [wp_nil]
  wp_alloc_window_lists [gridFinishFrame, gridLoopFrame, func36Def]
  simpa only [hOutput] using hArray

/-- Exact grid export for all raw ratios and input shapes under explicit bounded arena assumptions. -/
theorem stepCheckedBits_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer allocs releases frees : UInt64)
    (base : Nat) (input : Array UInt64)
    (hReady : GridEntryReady initial pointer input base allocs releases frees) :
    TerminatesWith env m 36 initial [.i64 pointer, .i64 ratio]
      (fun final values => ∃ root, values = [.i64 root] ∧ UInt64Array.At final root (Model.stepCheckedBits ratio input)) := by
  cases hInvalid : gridEntryInvalid ratio input.size
  · exact step_valid_entry_exact layout env initial ratio pointer allocs releases frees base input hReady hInvalid
  · have hRun := step_rejected_entry_exact layout env initial ratio pointer
      (arenaHeap base (1 + 6 * (input.size / 3)) 0) allocs input hReady.inputAt hInvalid
      hReady.invalid_fit hReady.pages hReady.heap hReady.freeHead hReady.allocations
    apply hRun.mono
    rintro final values ⟨hFinal, hValues, hArray⟩
    refine ⟨arenaHeap base (1 + 6 * (input.size / 3)) 0 + 48, hValues, ?_⟩
    have hModel : Model.stepCheckedBits ratio input = #[1] := by
      change (if gridEntryInvalid ratio input.size then _ else _) = _
      rw [hInvalid]
      rfl
    rw [hModel]
    exact hArray

#print axioms step_valid_entry_exact
#print axioms stepCheckedBits_exact_in_module
end Project.EulerGridStep.Execution
