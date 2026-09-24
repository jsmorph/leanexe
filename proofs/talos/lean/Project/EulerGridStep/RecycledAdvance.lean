import Project.EulerGridStep.AdvanceReusedProtected
import Project.EulerGridStep.RecycledCleanup
import Project.EulerGridStep.RejectedBuffers
import Project.EulerGridStep.GridSizes

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- The cell call preserves the old payload needed by the emitted loop condition;
    its pending owner release restores a six-buffer pool. -/
def RecycledAdvancePost (m : Wasm.Module) (env : HostEnv Unit)
    (roots : Nat → UInt64) (pointer initialRoot ratio : UInt64)
    (input oldOutput initialOutput : Array UInt64) (index : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  ∃ nextRoots : Nat → UInt64,
    values = [.i64 (nextRoots 0), .i64 (nextRoots 0)] ∧ nextRoots 0 ≠ 0 ∧
    roots 0 ≠ nextRoots 0 ∧ nextRoots 0 ≠ initialRoot ∧
    UInt64Array.At final (roots 0) oldOutput ∧
    TerminatesWith env m 40 final [.i64 (roots 0)]
      (fun after returned => returned = [] ∧ ∃ a r f,
        RecycledPool after nextRoots pointer initialRoot input (Model.advanceAt ratio input oldOutput index) a r f ∧
        after.mem.pages = final.mem.pages ∧ UInt64Array.At after pointer input ∧
        (⟨initialRoot, initialOutput⟩ : LiveBuffer).At after oldOutput.size)

/-- Both numerical outcomes are compatible with the loop's next recycling step. -/
theorem recycled_advance {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (roots : Nat → UInt64)
    (ratio inputUnused pointer unused initialRoot allocs releases frees : UInt64)
    (input output initialOutput : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hPool : RecycledPool initial roots pointer initialRoot input output allocs releases frees)
    (hInitial : (⟨initialRoot, initialOutput⟩ : LiveBuffer).At initial output.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (roots 0), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (RecycledAdvancePost m env roots pointer initialRoot ratio input output initialOutput index) := by
  let next := Model.advanceAt ratio input output index
  have hNextSize : next.size = output.size := advanceAt_size ratio input output index
  by_cases hAccepted : (Model.cellAt ratio input index).status = 0
  · apply (advanceAt_reused_protected layout env initial ratio inputUnused pointer unused allocs releases frees
      roots input output index hInput hi hAccepted (by omega)
      (by simpa only [cellLive] using hPool.buffers) hPool.separate hPool.inputSeparate
      ⟨initialRoot, initialOutput⟩ hInitial (fun a _ ha => hPool.initialSeparate a ha)).mono
    rintro final values ⟨hv, hBuffers, _, hInputFinal, hInitialFinal⟩
    refine ⟨roots ∘ acceptedPoolSlot, hv, (by
      intro hz
      have h48 := (hBuffers.liveAt ⟨roots 6, next⟩ (by simp [next])).2.1.root48
      change roots 6 = 0 at hz
      rw [hz] at h48
      contradiction),
      objectsSeparate_ne (hPool.separate 0 (by decide) 6 (by decide) (by decide)),
      objectsSeparate_ne (hPool.initialSeparate 6 (by decide)),
      (hBuffers.liveAt ⟨roots 0, output⟩ (by simp)).2.2, ?_⟩
    apply (recycled_accepted_cleanup layout env final roots pointer initialRoot
      (allocs + 6) (releases + 5) (frees + 5) input output next initialOutput hNextSize
      hPool.toRecycledGeometry hBuffers hInputFinal hInitialFinal).mono
    rintro after returned ⟨hr, hState, hp, hin, hinit⟩
    exact ⟨hr, _, _, _, hState, hp, hin, by simpa only [hNextSize] using hinit⟩
  · have hFree : ∀ root ∈ [roots 2, roots 3, roots 4, roots 5, roots 6],
        ObjectsSeparate (roots 1) output.size root output.size := by
      intro root hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      all_goals exact hPool.separate 1 (by decide) _ (by decide) (by decide)
    apply (advanceAt_rejected_reuse_buffers layout env initial ratio inputUnused pointer unused
      (roots 0) (roots 1) allocs releases frees input output index
      [roots 2, roots 3, roots 4, roots 5, roots 6] hInput hi hAccepted (by omega) hPool.buffers
      (hPool.separate 1 (by decide) 0 (by decide) (by decide)) hFree (hPool.inputSeparate 1 (by decide))).mono
    rintro final values ⟨hv, hBuffers, _, _, hResult, hInputFinal⟩
    have hInitialFinal := hResult.preserves_buffer _ _ hInitial (hPool.initialSeparate 1 (by decide))
    refine ⟨roots ∘ rejectedPoolSlot, hv, (by
      intro hz
      have h48 := (hBuffers.liveAt ⟨roots 1, next⟩ (by simp [next])).2.1.root48
      change roots 1 = 0 at hz
      rw [hz] at h48
      contradiction),
      objectsSeparate_ne (hPool.separate 0 (by decide) 1 (by decide) (by decide)),
      objectsSeparate_ne (hPool.initialSeparate 1 (by decide)),
      (hBuffers.liveAt ⟨roots 0, output⟩ (by simp)).2.2, ?_⟩
    apply (recycled_rejected_cleanup layout env final roots pointer initialRoot
      (allocs + 1) releases frees input output next initialOutput hNextSize
      hPool.toRecycledGeometry hBuffers hInputFinal hInitialFinal).mono
    rintro after returned ⟨hr, hState, hp, hin, hinit⟩
    exact ⟨hr, _, _, _, hState, hp, hin, by simpa only [hNextSize] using hinit⟩

#print axioms recycled_advance
end Project.EulerGridStep.Execution
