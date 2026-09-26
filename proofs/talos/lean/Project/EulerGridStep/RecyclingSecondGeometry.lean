import Project.EulerGridStep.RecyclingTransition

namespace Project.EulerGridStep.Execution
open Wasm

theorem recycling_second_geometry (base : Nat) (pointer : UInt64) (input output : Array UInt64)
    (hLoop : 1 < input.size / 3)
    (hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ 4294967296)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    RecycledGeometry (laterRoots base output.size 1) pointer (arenaRoot base output.size 0)
      input.size output.size := by
  refine ⟨later_roots_separate base output.size (input.size / 3) 1 (by decide) hLoop hBudget32,
    ?_, ?_⟩
  · intro a ha
    exact hSeparate (laterSlot 1 a) (later_slot_bound _ _ _ hLoop ha)
  · intro a ha
    have hPositive : 0 < laterSlot 1 a := by
      unfold laterSlot
      split <;> (try split) <;> omega
    exact arena_roots_separate_of_lt base output.size (laterSlot 1 a) 0 (input.size / 3 + 6)
      (later_slot_bound _ _ _ hLoop ha) (by omega) (by omega) hBudget32

#print axioms recycling_second_geometry
end Project.EulerGridStep.Execution
