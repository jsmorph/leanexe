import Project.EulerGridStep.EntryGuards
import Project.EulerGridStep.InvalidEntry

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem grid_guard_params (ratio pointer : UInt64) (length : Nat) :
    (gridGuardFrame ratio pointer length).params.length = 2 := rfl

theorem grid_guard_locals (ratio pointer : UInt64) (length : Nat) :
    (gridGuardFrame ratio pointer length).locals.length = 43 := by
  unfold gridGuardFrame
  split <;> simp_all [gridEntryFrame]
  split <;> simp

/-- Complete grid function for every entry rejection, with its exact singleton and store. -/
theorem step_rejected_entry_exact {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer heap allocs : UInt64) (input : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hInvalid : gridEntryInvalid ratio input.size = true)
    (hFit : heap.toNat + 48 + 16 ≤ initial.mem.pages * 65536) (hPages : initial.mem.pages ≤ 65536)
    (hHeap : initial.globals.globals[0]? = some (.i64 heap))
    (hFree : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs)) :
    TerminatesWith env m 36 initial [.i64 pointer, .i64 ratio]
      (fun final values => final = invalidEntryStore initial heap allocs ∧
        values = [.i64 (heap + 48)] ∧ UInt64Array.At final (heap + 48) #[1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func36Def)
    (by simpa [layout.noImports] using layout.step) ?_ (by simp [layout.noImports])
  change wp m func36 _ initial (gridEntryFrame ratio pointer) env
  rw [grid_function_shape]
  apply grid_entry_guards_spec layout env initial ratio pointer input hInput
  have hGuard : gridGuardFrame ratio pointer input.size =
      { gridGuardFrame ratio pointer input.size with values := [.i32 1] } := by
    simp [gridGuardFrame, hInvalid]
  rw [hGuard]
  change wp m [.iff 0 0 gridInvalidBody gridValidBody, .localGet 32] _ initial
    { gridGuardFrame ratio pointer input.size with values := [.i32 1] } env
  apply wp_iff_cons rfl
  rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
  change wp m (gridInvalidBody ++ []) _ initial
    { gridGuardFrame ratio pointer input.size with values := [] } env
  apply invalid_entry_spec m env initial { gridGuardFrame ratio pointer input.size with values := [] }
    heap allocs (grid_guard_params ratio pointer input.size) (grid_guard_locals ratio pointer input.size) rfl hFit hPages layout.memory32
    hHeap hFree hAllocs _ []
  intro hArray
  rw [wp_nil]
  wp_alloc_window_lists [invalidEntryResultFrame, invalidEntryFreshAllocFrame, invalidEntryFreshBumpFrame,
    FixedArrayCapacity.capacityFrame, func36Def, grid_guard_params, grid_guard_locals]
  exact hArray

#print axioms grid_guard_params
#print axioms grid_guard_locals
#print axioms step_rejected_entry_exact
end Project.EulerGridStep.Execution
