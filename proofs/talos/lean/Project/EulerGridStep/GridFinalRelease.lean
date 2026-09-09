import Project.EulerGridStep.GridFinalGeometry
import Project.EulerGridStep.ReleaseHeap

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The emitted final release frees only initial slot zero and preserves the returned output. -/
theorem grid_final_release {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (base cells index : Nat)
    (output : Array UInt64) (allocs releases frees : UInt64)
    (hPositive : 0 < index) (hIndex : index ≤ cells)
    (hStorage : GridLoopStorage initial base cells index output allocs releases frees)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size) :
    TerminatesWith env m 40 initial [.i64 (arenaRoot base output.size 0)]
      (fun final values => values = [] ∧
        UInt64Array.At final (gridLoopRoot base output.size index output[0]!) output ∧
        BufferState final output.size [⟨gridLoopRoot base output.size index output[0]!, output⟩]
          (arenaRoot base output.size 0 :: gridLoopPool base output.size index output[0]!)
          allocs (releases + 1) (frees + 1) ∧
        final.globals.globals[0]? = initial.globals.globals[0]? ∧
        final.mem.pages = initial.mem.pages) := by
  have hBuffers := hStorage.buffers
  have hBudget := hStorage.budget
  have hPages := hBuffers.pages
  have hBudget32 : base + (cells + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hLive : ∀ buffer ∈ [⟨gridLoopRoot base output.size index output[0]!, output⟩],
      ObjectsSeparate (arenaRoot base output.size 0) output.size (buffer : LiveBuffer).root output.size := by
    intro buffer hMem
    obtain rfl := List.mem_singleton.mp hMem
    exact gridLoopRoot_separate_zero base output.size cells index output[0]! hPositive hIndex hBudget32
  have hFree := gridLoopPool_separate_zero base output.size cells index output[0]! hBudget32
  have hCall := release_owned_buffer_state_heap layout env initial (arenaRoot base output.size 0)
    allocs releases frees (Array.replicate output.size 0)
    [⟨gridLoopRoot base output.size index output[0]!, output⟩]
    (gridLoopPool base output.size index output[0]!)
    (by simpa only [Array.size_replicate] using hProtected.2.1) hProtected.2.2
    (by simpa only [Array.size_replicate] using hBuffers)
    (by simpa only [Array.size_replicate] using hLive)
    (by simpa only [Array.size_replicate] using hFree)
  simp only [Array.size_replicate] at hCall
  apply hCall.mono
  rintro final values ⟨hValues, hRelease, hFinalBuffers, hHeap⟩
  exact ⟨hValues, (hFinalBuffers.liveAt ⟨gridLoopRoot base output.size index output[0]!, output⟩ (by simp)).2.2,
    hFinalBuffers, hHeap, hRelease.pages⟩

theorem grid_loop_done_positive {current : Store Unit} {base cells index : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64} (h : GridLoopStorage current base cells index output allocs releases frees)
    (hCells : 0 < cells) (hDone : index = cells ∨ output[0]! ≠ 0) : 0 < index := by
  cases h with
  | initial a r f hBuffers hHeap hBudget =>
      simp at hDone
      omega
  | accepted i out a r f hi hs hArena => exact hi
  | rejected i out a r f hi hArena => exact hi

#print axioms grid_final_release
#print axioms grid_loop_done_positive
end Project.EulerGridStep.Execution
