import Project.EulerGridStep.RotatingArenaState
import Project.EulerGridStep.RejectedBuffers
import Project.EulerGridStep.ProtectedBuffer

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

def rotatingPoolTail (base count completed : Nat) : List UInt64 :=
  if completed = 1 then writerPool (rotatingRoots base count completed) 1
  else reusePool (rotatingRoots base count completed) 1

theorem rotatingPool_head (base count completed : Nat) :
    rotatingPool base count completed =
      rotatingRoots base count completed 1 :: rotatingPoolTail base count completed := by
  unfold rotatingPool rotatingPoolTail
  split_ifs
  · exact writerPool_head _ 0 (by decide)
  · exact reusePool_head _ 0 (by decide)

theorem advanceAt_rotating_rejected {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < index) (hi : index < input.size / 3)
    (hRejected : (Model.cellAt ratio input index).status ≠ 0)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hState : RotatingArenaState initial base (input.size / 3) index output allocs releases frees)
    (initialOutput : Array UInt64)
    (hProtected : (⟨arenaRoot base output.size 0, initialOutput⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (rotatingRoots base output.size index 0), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values =>
        values = [.i64 (rotatingRoots base output.size index 1), .i64 (rotatingRoots base output.size index 1)] ∧
        BufferState final output.size
          [⟨rotatingRoots base output.size index 1, Model.advanceAt ratio input output index⟩,
            ⟨rotatingRoots base output.size index 0, output⟩]
          (rotatingPoolTail base output.size index) (allocs + 1) releases frees ∧
        final.globals.globals[0]? = some (.i64 (arenaHeap base output.size (rotatingHeapSlot index))) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        (⟨arenaRoot base output.size 0, initialOutput⟩ : LiveBuffer).At final output.size) := by
  have hBudget := hState.eight_slot_bound hPositive hi
  have hSlots := rotatingRoots_separate base output.size index hBudget
  have hInputSeparate : ObjectsSeparate (rotatingRoots base output.size index 1) output.size pointer input.size := by
    have hBound := rotatingSlot_bounds (index - 1) 1 (by decide)
    exact hSeparate _ (by omega)
  have hFree : ∀ other ∈ rotatingPoolTail base output.size index,
      ObjectsSeparate (rotatingRoots base output.size index 1) output.size other output.size := by
    unfold rotatingPoolTail
    split_ifs
    · exact writerPool_separate _ output.size 1 1 (by decide) (by decide) hSlots
    · exact reusePool_separate _ output.size 1 1 (by decide) (by decide) hSlots
  have hCall := advanceAt_rejected_reuse_buffers layout env initial ratio inputUnused pointer unused
    (rotatingRoots base output.size index 0) (rotatingRoots base output.size index 1)
    allocs releases frees input output index (rotatingPoolTail base output.size index)
    hInput hi hRejected (by omega) (by simpa only [rotatingPool_head] using hState.buffers)
    (hSlots 1 (by decide) 0 (by decide) (by decide)) hFree hInputSeparate
  apply hCall.mono
  rintro final values ⟨hValues, hBuffers, hHeap, hPages, hResult, hInputFinal⟩
  exact ⟨hValues, hBuffers, hHeap.trans hState.heap, hPages, hInputFinal,
    hResult.preserves_buffer _ output.size hProtected
      (rotatingRoots_initial_separate base output.size index 1 (by decide) hBudget)⟩

#print axioms rotatingPool_head
#print axioms advanceAt_rotating_rejected
end Project.EulerGridStep.Execution
