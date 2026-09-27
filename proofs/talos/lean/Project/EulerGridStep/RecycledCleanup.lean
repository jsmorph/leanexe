import Project.EulerGridStep.RecycledPool
import Project.EulerGridStep.ReleasePrevious

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- Releasing the old result completes the rotation after six reused clones. -/
theorem recycled_accepted_cleanup {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (roots : Nat → UInt64)
    (pointer initialRoot allocs releases frees : UInt64) (input oldOutput nextOutput initialOutput : Array UInt64)
    (hSize : nextOutput.size = oldOutput.size)
    (hGeometry : RecycledGeometry roots pointer initialRoot input.size oldOutput.size)
    (hState : BufferState initial oldOutput.size [⟨roots 6, nextOutput⟩, ⟨roots 0, oldOutput⟩]
      [roots 1, roots 2, roots 3, roots 4, roots 5] allocs releases frees)
    (hInput : UInt64Array.At initial pointer input)
    (hInitial : (⟨initialRoot, initialOutput⟩ : LiveBuffer).At initial oldOutput.size) :
    TerminatesWith env m 40 initial [.i64 (roots 0)]
      (fun final values => values = [] ∧
        RecycledPool final (roots ∘ acceptedPoolSlot) pointer initialRoot input nextOutput
          allocs (releases + 1) (frees + 1) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        (⟨initialRoot, initialOutput⟩ : LiveBuffer).At final nextOutput.size) := by
  have hFree : ∀ root ∈ [roots 1, roots 2, roots 3, roots 4, roots 5],
      ObjectsSeparate (roots 0) oldOutput.size root oldOutput.size := by
    intro root hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals exact hGeometry.separate 0 (by decide) _ (by decide) (by decide)
  apply (release_previous_output layout env initial (roots 0) (roots 6) allocs releases frees
    oldOutput nextOutput [roots 1, roots 2, roots 3, roots 4, roots 5] hSize hState
    (hGeometry.separate 0 (by decide) 6 (by decide) (by decide)) hFree
    (fun final => UInt64Array.At final pointer input ∧
      (⟨initialRoot, initialOutput⟩ : LiveBuffer).At final nextOutput.size) (by
        intro final hResult
        refine ⟨hResult.preserves_array pointer input hInput (hGeometry.inputSeparate 0 (by decide)), ?_⟩
        rw [hSize]
        exact hResult.preserves_buffer _ _ hInitial (hGeometry.initialSeparate 0 (by decide)))).mono
  rintro final values ⟨hv, hBuffers, hPages, hInputFinal, hInitialFinal⟩
  refine ⟨hv, ⟨?_, ?_⟩, hPages, hInputFinal, hInitialFinal⟩
  · rw [hSize]
    exact hGeometry.relabel acceptedPoolSlot (fun _ hi => acceptedPoolSlot_bound hi)
      (fun _ hi _ hj h => acceptedPoolSlot_injective hi hj h)
  · simpa [Function.comp_def, acceptedPoolSlot]
      using hBuffers

/-- Releasing the old result completes the rotation after one rejected status clone. -/
theorem recycled_rejected_cleanup {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (roots : Nat → UInt64)
    (pointer initialRoot allocs releases frees : UInt64) (input oldOutput nextOutput initialOutput : Array UInt64)
    (hSize : nextOutput.size = oldOutput.size)
    (hGeometry : RecycledGeometry roots pointer initialRoot input.size oldOutput.size)
    (hState : BufferState initial oldOutput.size [⟨roots 1, nextOutput⟩, ⟨roots 0, oldOutput⟩]
      [roots 2, roots 3, roots 4, roots 5, roots 6] allocs releases frees)
    (hInput : UInt64Array.At initial pointer input)
    (hInitial : (⟨initialRoot, initialOutput⟩ : LiveBuffer).At initial oldOutput.size) :
    TerminatesWith env m 40 initial [.i64 (roots 0)]
      (fun final values => values = [] ∧
        RecycledPool final (roots ∘ rejectedPoolSlot) pointer initialRoot input nextOutput
          allocs (releases + 1) (frees + 1) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        (⟨initialRoot, initialOutput⟩ : LiveBuffer).At final nextOutput.size) := by
  have hFree : ∀ root ∈ [roots 2, roots 3, roots 4, roots 5, roots 6],
      ObjectsSeparate (roots 0) oldOutput.size root oldOutput.size := by
    intro root hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals exact hGeometry.separate 0 (by decide) _ (by decide) (by decide)
  apply (release_previous_output layout env initial (roots 0) (roots 1) allocs releases frees
    oldOutput nextOutput [roots 2, roots 3, roots 4, roots 5, roots 6] hSize hState
    (hGeometry.separate 0 (by decide) 1 (by decide) (by decide)) hFree
    (fun final => UInt64Array.At final pointer input ∧
      (⟨initialRoot, initialOutput⟩ : LiveBuffer).At final nextOutput.size) (by
        intro final hResult
        refine ⟨hResult.preserves_array pointer input hInput (hGeometry.inputSeparate 0 (by decide)), ?_⟩
        rw [hSize]
        exact hResult.preserves_buffer _ _ hInitial (hGeometry.initialSeparate 0 (by decide)))).mono
  rintro final values ⟨hv, hBuffers, hPages, hInputFinal, hInitialFinal⟩
  refine ⟨hv, ⟨?_, ?_⟩, hPages, hInputFinal, hInitialFinal⟩
  · rw [hSize]
    exact hGeometry.relabel rejectedPoolSlot (fun _ hi => rejectedPoolSlot_bound hi)
      (fun _ _ _ _ h => rejectedPoolSlot_injective h)
  · simpa [Function.comp_def, rejectedPoolSlot]
      using hBuffers

#print axioms recycled_accepted_cleanup
#print axioms recycled_rejected_cleanup
end Project.EulerGridStep.Execution
