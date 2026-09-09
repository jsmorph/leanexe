import Project.EulerGridStep.AdvanceMixedProtected
import Project.EulerGridStep.LaterArenaState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A complete later accepted advance preserves the growing arena invariant. -/
theorem advanceAt_later_protected {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < index) (hi : index < input.size / 3)
    (hAccepted : (Model.cellAt ratio input index).status = 0)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hState : LaterArenaState initial base (input.size / 3) index output allocs releases frees)
    (initialOutput : Array UInt64)
    (hProtected : (⟨arenaRoot base output.size 0, initialOutput⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (arenaRoot base output.size (index + 5)), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (arenaRoot base output.size (index + 6)),
          .i64 (arenaRoot base output.size (index + 6))] ∧
        LaterArenaState final base (input.size / 3) (index + 1) (Model.advanceAt ratio input output index)
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        UInt64Array.At final (arenaRoot base output.size (index + 5)) output ∧
        (⟨arenaRoot base output.size 0, initialOutput⟩ : LiveBuffer).At final output.size) := by
  have hBudget := hState.budget
  have hPagesBound := hState.buffers.pages
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hProtectedSeparate : ∀ a, 1 ≤ a → a ≤ 6 →
      ObjectsSeparate (laterRoots base output.size index a) output.size (arenaRoot base output.size 0) output.size := by
    intro a hLo hHi
    have hSlotPositive : 0 < laterSlot index a := by
      simp only [laterSlot, Nat.ne_of_gt hLo, ite_false]
      split <;> omega
    exact arena_roots_separate_of_lt base output.size (laterSlot index a) 0 (input.size / 3 + 6)
      (later_slot_bound _ _ _ hi hHi) (by omega) (by omega) hBudget32
  have hCall := advanceAt_mixed_protected layout env initial ratio inputUnused pointer unused
    (arenaHeap base output.size (index + 6)) allocs releases frees (laterRoots base output.size index)
    input output index hInput hi hAccepted (by omega) (hState.mixed _ hi)
    (later_root_six base output.size index)
    (later_roots_separate base output.size (input.size / 3) index hPositive hi hBudget32)
    (fun a ha => hSeparate (laterSlot index a) (later_slot_bound _ _ _ hi ha))
    ⟨arenaRoot base output.size 0, initialOutput⟩ hProtected hProtectedSeparate
  rw [later_root_zero] at hCall
  apply hCall.mono
  rintro final values ⟨hValues, hBuffers, hHeap, hPages, hInputFinal, hProtectedFinal⟩
  have hSourceFinal : UInt64Array.At final (arenaRoot base output.size (index + 5)) output :=
    (hBuffers.liveAt ⟨arenaRoot base output.size (index + 5), output⟩ (by simp)).2.2
  have hKeep := hBuffers.restrict_live
    [⟨laterRoots base output.size index 6, Model.advanceAt ratio input output index⟩]
    (by intro buffer hb; obtain rfl := List.mem_singleton.mp hb; exact List.mem_cons_self)
  change BufferState final output.size
    [⟨laterRoots base output.size index 6, Model.advanceAt ratio input output index⟩]
    (writerPool (laterRoots base output.size index) 0) (allocs + 6) (releases + 5) (frees + 5) at hKeep
  have hRoot : laterRoots base output.size index 6 = arenaRoot base output.size (index + 1 + 5) := by
    simp only [laterRoots, laterSlot, show ¬ (6 : Nat) = 0 by decide, ite_false, ite_true]
  rw [later_pool, hRoot] at hKeep
  refine ⟨?_, ⟨?_, ?_, ?_⟩, hPages, hInputFinal, hSourceFinal, hProtectedFinal⟩
  · simpa [laterRoots, laterSlot] using hValues
  · simpa only [advanceAt_size] using hKeep
  · simpa only [advanceAt_size, show index + 1 + 6 = (index + 6) + 1 by omega,
      arena_heap_succ] using hHeap
  · simpa only [advanceAt_size, hPages] using hBudget

#print axioms advanceAt_later_protected
end Project.EulerGridStep.Execution
