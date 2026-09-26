import Project.EulerGridStep.GridLoopTransition
import Project.EulerGridStep.ReleasePreviousOutput

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

def gridPendingPool (base count index : Nat) (status : UInt64) : List UInt64 :=
  if status = 0 then writerPool (rotatingRoots base count index) 0
  else rotatingPoolTail base count index

def gridPendingHeapSlot (index : Nat) (status : UInt64) : Nat :=
  if status = 0 then 8 else rotatingHeapSlot index

theorem grid_rotating_release {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (base cells index : Nat)
    (pointer allocs releases frees status : UInt64) (input oldOutput newOutput : Array UInt64)
    (hi : 0 < index) (hSize : newOutput.size = oldOutput.size)
    (hHeader : newOutput[0]! = if status = 0 then 0 else 1)
    (hBuffers : BufferState initial oldOutput.size
      [⟨rotatingRoots base oldOutput.size index (if status = 0 then 6 else 1), newOutput⟩,
        ⟨rotatingRoots base oldOutput.size index 0, oldOutput⟩]
      (gridPendingPool base oldOutput.size index status) allocs releases frees)
    (hHeap : initial.globals.globals[0]? =
      some (.i64 (arenaHeap base oldOutput.size (gridPendingHeapSlot index status))))
    (hBudget : base + (cells + 6) * arenaObjectSize oldOutput.size ≤ initial.mem.pages * 65536)
    (hEight : base + 8 * arenaObjectSize oldOutput.size ≤ 4294967296)
    (hInput : UInt64Array.At initial pointer input)
    (hInputSeparate : ObjectsSeparate (rotatingRoots base oldOutput.size index 0) oldOutput.size pointer input.size)
    (hProtected : (⟨arenaRoot base oldOutput.size 0, Array.replicate oldOutput.size 0⟩ : LiveBuffer).At initial oldOutput.size) :
    TerminatesWith env m 40 initial [.i64 (rotatingRoots base oldOutput.size index 0)]
      (fun final values => values = [] ∧
        GridLoopStorage final base cells (index + 1) newOutput allocs (releases + 1) (frees + 1) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        (⟨arenaRoot base oldOutput.size 0, Array.replicate oldOutput.size 0⟩ : LiveBuffer).At final oldOutput.size) := by
  have hSlots := rotatingRoots_separate base oldOutput.size index hEight
  have hNew : ObjectsSeparate (rotatingRoots base oldOutput.size index 0) oldOutput.size
      (rotatingRoots base oldOutput.size index (if status = 0 then 6 else 1)) oldOutput.size := by
    split_ifs <;> exact hSlots 0 (by decide) _ (by decide) (by decide)
  have hFree : ∀ other ∈ gridPendingPool base oldOutput.size index status,
      ObjectsSeparate (rotatingRoots base oldOutput.size index 0) oldOutput.size other oldOutput.size := by
    unfold gridPendingPool rotatingPoolTail
    split_ifs
    · exact writerPool_separate _ _ 0 0 (by decide) (by decide) hSlots
    · exact writerPool_separate _ _ 0 1 (by decide) (by decide) hSlots
    · exact reusePool_separate _ _ 0 1 (by decide) (by decide) hSlots
  have hCall := release_previous_output_framed layout env initial
    (rotatingRoots base oldOutput.size index 0)
    (rotatingRoots base oldOutput.size index (if status = 0 then 6 else 1))
    allocs releases frees oldOutput newOutput (gridPendingPool base oldOutput.size index status)
    hSize hBuffers hNew hFree
    (fun final => UInt64Array.At final pointer input ∧
      (⟨arenaRoot base oldOutput.size 0, Array.replicate oldOutput.size 0⟩ : LiveBuffer).At final oldOutput.size)
    (fun final hResult => ⟨hResult.preserves_array pointer input hInput hInputSeparate,
      hResult.preserves_buffer _ _ hProtected
        (rotatingRoots_initial_separate base oldOutput.size index 0 (by decide) hEight)⟩)
  apply hCall.mono
  rintro final values ⟨hValues, hFinal, hHeapFinal, hPages, hInputFinal, hProtectedFinal⟩
  refine ⟨hValues, ?_, hPages, hInputFinal, hProtectedFinal⟩
  have hBudgetFinal : base + (cells + 6) * arenaObjectSize newOutput.size ≤ final.mem.pages * 65536 := by
    simpa only [hSize, hPages] using hBudget
  have hHeapResult := hHeapFinal.trans hHeap
  by_cases hs : status = 0
  · refine .accepted _ _ _ _ _ (by omega) (by simpa only [hs, ite_true] using hHeader) ?_
    refine ⟨?_, ?_, hBudgetFinal⟩
    · simpa only [hSize, rotatingPool, show index + 1 ≠ 1 by omega, ite_false,
        rotatingRoots_succ base oldOutput.size index 0 hi, rotateIndex, ite_true,
        rotatingRoots_pool_succ base oldOutput.size index hi, gridPendingPool, hs] using hFinal
    · simpa only [hSize, rotatingHeapSlot, show index + 1 ≠ 1 by omega, ite_false,
        gridPendingHeapSlot, hs, ite_true] using hHeapResult
  · refine .rejected _ _ _ _ _ (by omega) ?_
    refine ⟨?_, ?_, hBudgetFinal, by simpa only [hs, ite_false] using hHeader⟩
    · simpa only [hSize, rotatingRejectedRoot, rotatingRejectedPool,
        show index + 1 ≠ 1 by omega, ite_false, Nat.add_sub_cancel, gridPendingPool, hs] using hFinal
    · simpa only [hSize, rotatingRejectedHeapSlot, show index + 1 ≠ 1 by omega,
        ite_false, Nat.add_sub_cancel, gridPendingHeapSlot, hs] using hHeapResult

#print axioms grid_rotating_release
end Project.EulerGridStep.Execution
