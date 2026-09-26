import Project.EulerGridStep.RecyclingSecondGeometry
import Project.EulerGridStep.RecyclingStateFacts

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- The second accepted call supplies the seventh reusable slot; rejection stops with its smaller pool. -/
theorem recycling_second_transition {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hLoop : 1 < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hState : LaterArenaState initial base (input.size / 3) 1 output allocs releases frees)
    (hInitial : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 1, .i64 (arenaRoot base output.size 6), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (RecyclingAdvancePost m env base pointer ratio (arenaRoot base output.size 6) input output 1) := by
  let roots := laterRoots base output.size 1
  let next := Model.advanceAt ratio input output 1
  have hNextSize : next.size = output.size := advanceAt_size ratio input output 1
  have hBudget := hState.budget
  have hPages := hState.buffers.pages
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hGeometry := recycling_second_geometry base pointer input output hLoop hBudget32 hSeparate
  change RecycledGeometry roots pointer (arenaRoot base output.size 0) input.size output.size at hGeometry
  have hOldNe := objectsSeparate_ne (hGeometry.initialSeparate 0 (by decide))
  change arenaRoot base output.size 6 ≠ arenaRoot base output.size 0 at hOldNe
  by_cases hAccepted : (Model.cellAt ratio input 1).status = 0
  · apply (advanceAt_mixed_protected layout env initial ratio inputUnused pointer unused
      (arenaHeap base output.size 7) allocs releases frees roots input output 1 hInput hLoop hAccepted
      (by omega) (hState.mixed _ hLoop) (later_root_six base output.size 1)
      hGeometry.separate hGeometry.inputSeparate _ hInitial
      (fun a _ ha => hGeometry.initialSeparate a ha)).mono
    rintro final values ⟨hv, hBuffers, _, _, hin, hInitialFinal⟩
    refine ⟨roots 6, hv, liveBuffer_root_nonzero
      (hBuffers.liveAt ⟨roots 6, next⟩ (by simp [next])), objectsSeparate_ne (hGeometry.separate 0 (by decide) 6 (by decide) (by decide)),
      objectsSeparate_ne (hGeometry.initialSeparate 6 (by decide)),
      (hBuffers.liveAt ⟨roots 0, output⟩ (by simp)).2.2,
      fun h => False.elim (hOldNe h), fun _ => ?_⟩
    apply (recycled_accepted_cleanup layout env final roots pointer (arenaRoot base output.size 0)
      (allocs + 6) (releases + 5) (frees + 5) input output next (Array.replicate output.size 0)
      hNextSize hGeometry hBuffers hin hInitialFinal).mono
    rintro after returned ⟨hr, hPool, _, hInputAfter, hInitialAfter⟩
    refine ⟨hr, ?_, hInputAfter, ?_⟩
    · apply RecycledPool.recyclingState (roots := roots ∘ acceptedPoolSlot)
      simpa only [advanceAt_size] using hPool
    · simpa only [hNextSize] using hInitialAfter
  · have hFree : ∀ root ∈ [roots 2, roots 3, roots 4, roots 5],
        ObjectsSeparate (roots 1) output.size root output.size := by
      intro root hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals exact hGeometry.separate 1 (by decide) _ (by decide) (by decide)
    apply (advanceAt_rejected_reuse_buffers layout env initial ratio inputUnused pointer unused
      (roots 0) (roots 1) allocs releases frees input output 1 [roots 2, roots 3, roots 4, roots 5]
      hInput hLoop hAccepted (by omega) (by simpa [roots, laterRoots, laterSlot, writerPool] using hState.buffers)
      (hGeometry.separate 1 (by decide) 0 (by decide) (by decide)) hFree
      (hGeometry.inputSeparate 1 (by decide))).mono
    rintro final values ⟨hv, hBuffers, _, _, hResult, hin⟩
    have hInitialFinal := hResult.preserves_buffer _ _ hInitial (hGeometry.initialSeparate 1 (by decide))
    have hFreeOld : ∀ root ∈ [roots 2, roots 3, roots 4, roots 5],
        ObjectsSeparate (roots 0) output.size root output.size := by
      intro root hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals exact hGeometry.separate 0 (by decide) _ (by decide) (by decide)
    refine ⟨roots 1, hv, liveBuffer_root_nonzero
      (hBuffers.liveAt ⟨roots 1, next⟩ (by simp [next])), objectsSeparate_ne (hGeometry.separate 0 (by decide) 1 (by decide) (by decide)),
      objectsSeparate_ne (hGeometry.initialSeparate 1 (by decide)),
      (hBuffers.liveAt ⟨roots 0, output⟩ (by simp)).2.2,
      fun h => False.elim (hOldNe h), fun _ => ?_⟩
    apply (release_previous_output layout env final (roots 0) (roots 1) (allocs + 1) releases frees
      output next [roots 2, roots 3, roots 4, roots 5] hNextSize hBuffers
      (hGeometry.separate 0 (by decide) 1 (by decide) (by decide)) hFreeOld
      (fun after => UInt64Array.At after pointer input ∧
        (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At after output.size) (by
          intro after hRelease
          exact ⟨hRelease.preserves_array pointer input hin (hGeometry.inputSeparate 0 (by decide)),
            hRelease.preserves_buffer _ _ hInitialFinal (hGeometry.initialSeparate 0 (by decide))⟩)).mono
    rintro after returned ⟨hr, hBuffersAfter, _, hInputAfter, hInitialAfter⟩
    refine ⟨hr, ?_, hInputAfter, hInitialAfter⟩
    apply recycling_stopped_of_buffers hBuffersAfter
    · simpa only [hNextSize] using hGeometry.initialSeparate 1 (by decide)
    · have hs := advanceAt_rejected_status ratio input output 1 hAccepted (by omega)
      change next[0]! = 1 at hs
      rw [hs]
      decide

#print axioms recycling_second_transition
end Project.EulerGridStep.Execution
