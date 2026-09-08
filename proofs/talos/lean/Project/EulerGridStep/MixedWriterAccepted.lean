import Project.EulerGridStep.MixedWriterFramed

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

theorem mixedChoice_root (roots : Nat → UInt64) (heapTop allocs : UInt64) (count field : Nat)
    (hField : field < 6) (hRoot : roots 6 = heapTop + 48) :
    (mixedChoice roots heapTop allocs count field).root = roots (field + 1) := by
  by_cases hReuse : field < 5
  · simp only [mixedChoice, hReuse, ite_true, FieldAllocation.root]
  · have hFive : field = 5 := by omega
    simp [mixedChoice, hFive, FieldAllocation.root, hRoot]

/-- The actual later-cell writer preserves the old grid and exposes its one-object heap advance. -/
theorem writeCell_mixed_accepted_exact_in_module {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : MixedCellState initial heapTop roots output index cell 0 allocs releases frees)
    (hRoot : roots 6 = heapTop + 48)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (observedRoot : UInt64) (observed : Array UInt64)
    (hObserved : UInt64Array.At initial observedRoot observed)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) output.size observedRoot observed.size) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (roots 0), .i64 unused]
      (fun final values => values = [.i64 (roots 6), .i64 (roots 6)] ∧
        BufferState final output.size
          [⟨roots 6, Model.putCell output index cell⟩, ⟨roots 0, output⟩]
          [roots 1, roots 2, roots 3, roots 4, roots 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest output.size)) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final observedRoot observed) := by
  apply writeCell_mixed_framed layout env initial unused heapTop allocs releases frees roots output index
    cell hAccepted hi hState hRoot hSlots (fun current => UInt64Array.At current observedRoot observed)
    hObserved
  · intro field hField current final hOld hResult
    apply hResult.preserves_array observedRoot observed hOld
    simpa only [cellPrefix_size, mixedChoice_root roots heapTop allocs output.size field hField hRoot]
      using hSeparate (field + 1) (by omega)
  · intro count hLo hHi current final hOld hResult
    apply hResult.preserves_array observedRoot observed hOld
    simpa only [cellPrefix_size] using hSeparate count (by omega)

#print axioms mixedChoice_root
#print axioms writeCell_mixed_accepted_exact_in_module
end Project.EulerGridStep.Execution
