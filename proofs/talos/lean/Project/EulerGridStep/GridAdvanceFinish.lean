import Project.EulerGridStep.GridRotatingRelease

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

def GridNextState (current : Store Unit) (base index : Nat) (pointer : UInt64)
    (input output : Array UInt64) : Prop :=
  (∃ a r f, GridLoopStorage current base (input.size / 3) index output a r f) ∧
  UInt64Array.At current pointer input ∧
  (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At current output.size

def GridAdvanceFinish (m : Wasm.Module) (env : HostEnv Unit) (current : Store Unit)
    (base index : Nat) (pointer : UInt64) (input output next : Array UInt64) : Prop :=
  if index = 0 then GridNextState current base (index + 1) pointer input next
  else
    gridLoopRoot base output.size index output[0]! ≠ 0 ∧
    gridLoopRoot base output.size index output[0]! ≠ arenaRoot base output.size 0 ∧
    gridLoopRoot base output.size index output[0]! ≠ gridLoopRoot base next.size (index + 1) next[0]! ∧
    TerminatesWith env m 40 current [.i64 (gridLoopRoot base output.size index output[0]!)]
      (fun final values => values = [] ∧ GridNextState final base (index + 1) pointer input next)

theorem grid_positive_finish {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (base index : Nat)
    (ratio pointer allocs releases frees : UInt64) (input output : Array UInt64)
    (hi : 0 < index) (hSize : 0 < output.size) (hStatus : output[0]! = 0)
    (hBuffers : BufferState initial output.size
      [⟨rotatingRoots base output.size index (if (Model.cellAt ratio input index).status = 0 then 6 else 1),
          Model.advanceAt ratio input output index⟩,
        ⟨rotatingRoots base output.size index 0, output⟩]
      (gridPendingPool base output.size index (Model.cellAt ratio input index).status) allocs releases frees)
    (hHeap : initial.globals.globals[0]? = some (.i64
      (arenaHeap base output.size (gridPendingHeapSlot index (Model.cellAt ratio input index).status))))
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ initial.mem.pages * 65536)
    (hEight : base + 8 * arenaObjectSize output.size ≤ 4294967296)
    (hInput : UInt64Array.At initial pointer input)
    (hInputSeparate : ObjectsSeparate (rotatingRoots base output.size index 0) output.size pointer input.size)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size) :
    GridAdvanceFinish m env initial base index pointer input output (Model.advanceAt ratio input output index) := by
  have hOld := (hBuffers.liveAt ⟨rotatingRoots base output.size index 0, output⟩ (by simp)).2.1.root48
  have hInitial := (rotatingRoots_initial_separate base output.size index 0 (by decide) hEight).ne
  have hNew : rotatingRoots base output.size index 0 ≠
      rotatingRoots base output.size index (if (Model.cellAt ratio input index).status = 0 then 6 else 1) := by
    split_ifs <;> exact (rotatingRoots_separate base output.size index hEight 0 (by decide) _ (by decide) (by decide)).ne
  have hCall := grid_rotating_release layout env initial base (input.size / 3) index
    pointer allocs releases frees (Model.cellAt ratio input index).status input output
    (Model.advanceAt ratio input output index) hi (advanceAt_size ratio input output index)
    (advanceAt_header ratio input output index hSize hStatus) hBuffers hHeap hBudget hEight hInput hInputSeparate hProtected
  simp only [GridAdvanceFinish, Nat.ne_of_gt hi, ite_false]
  rw [gridLoopRoot_advance base index ratio input output hSize hStatus]
  simp only [gridLoopRoot, Nat.ne_of_gt hi, ite_false, hStatus, ite_true,
    gridAdvanceRoot, Nat.ne_of_gt hi, ite_false]
  refine ⟨?_, hInitial, hNew, ?_⟩
  · intro hZero
    rw [hZero] at hOld
    contradiction
  · apply hCall.mono
    rintro final values ⟨hValues, hStorage, hPages, hInputFinal, hProtectedFinal⟩
    exact ⟨hValues, ⟨allocs, releases + 1, frees + 1, hStorage⟩, hInputFinal,
      by simpa only [advanceAt_size] using hProtectedFinal⟩

#print axioms grid_positive_finish
end Project.EulerGridStep.Execution
