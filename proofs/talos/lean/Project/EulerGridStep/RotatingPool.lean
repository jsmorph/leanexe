import Project.EulerGridStep.LaterArena
import Project.EulerGridStep.ReusedState

namespace Project.EulerGridStep.Execution
open Wasm

def rotateIndex (field : Nat) : Nat := if field = 0 then 6 else field - 1

theorem rotateIndex_bound (field : Nat) (h : field ≤ 6) : rotateIndex field ≤ 6 := by
  unfold rotateIndex
  split_ifs <;> omega

theorem rotateIndex_injective (a b : Nat) (ha : a ≤ 6) (hb : b ≤ 6) (hne : a ≠ b) :
    rotateIndex a ≠ rotateIndex b := by
  unfold rotateIndex
  split_ifs <;> omega

def rotatingSlot : Nat → Nat → Nat
  | 0, field => laterSlot 1 field
  | turns + 1, field => rotatingSlot turns (rotateIndex field)

theorem rotatingSlot_bounds (turns field : Nat) (h : field ≤ 6) :
    1 ≤ rotatingSlot turns field ∧ rotatingSlot turns field ≤ 7 := by
  induction turns generalizing field with
  | zero => simp only [rotatingSlot, laterSlot]; split_ifs <;> omega
  | succ turns ih => exact ih _ (rotateIndex_bound field h)

theorem rotatingSlot_injective (turns a b : Nat) (ha : a ≤ 6) (hb : b ≤ 6) (hne : a ≠ b) :
    rotatingSlot turns a ≠ rotatingSlot turns b := by
  induction turns generalizing a b with
  | zero => exact later_slot_injective 1 a b (by decide) ha hb hne
  | succ turns ih =>
    exact ih _ _ (rotateIndex_bound a ha) (rotateIndex_bound b hb)
      (rotateIndex_injective a b ha hb hne)

def rotatingRoots (base count completed field : Nat) : UInt64 :=
  arenaRoot base count (rotatingSlot (completed - 1) field)

theorem rotatingRoots_succ (base count completed field : Nat) (h : 0 < completed) :
    rotatingRoots base count (completed + 1) field =
      rotatingRoots base count completed (rotateIndex field) := by
  unfold rotatingRoots
  rw [show completed + 1 - 1 = (completed - 1) + 1 by omega]
  rfl

theorem rotatingRoots_separate (base count completed : Nat)
    (hBudget : base + 8 * arenaObjectSize count ≤ 4294967296) :
    ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (rotatingRoots base count completed a) count
        (rotatingRoots base count completed b) count := by
  intro a ha b hb hne
  exact arena_roots_separate_of_lt base count _ _ 8
    (by have := rotatingSlot_bounds (completed - 1) a ha; omega)
    (by have := rotatingSlot_bounds (completed - 1) b hb; omega)
    (rotatingSlot_injective (completed - 1) a b ha hb hne) hBudget

theorem rotatingRoots_initial_separate (base count completed field : Nat) (hField : field ≤ 6)
    (hBudget : base + 8 * arenaObjectSize count ≤ 4294967296) :
    ObjectsSeparate (rotatingRoots base count completed field) count (arenaRoot base count 0) count := by
  have h := rotatingSlot_bounds (completed - 1) field hField
  exact arena_roots_separate_of_lt base count _ 0 8 (by omega) (by decide) (by omega) hBudget

theorem rotatingRoots_pool_succ (base count completed : Nat) (h : 0 < completed) :
    reusePool (rotatingRoots base count (completed + 1)) 0 =
      rotatingRoots base count completed 0 :: writerPool (rotatingRoots base count completed) 0 := by
  simp [reusePool, writerPool, List.range_succ, rotatingRoots_succ base count completed _ h,
    rotateIndex]

#print axioms rotatingSlot_bounds
#print axioms rotatingSlot_injective
#print axioms rotatingRoots_separate
#print axioms rotatingRoots_initial_separate
#print axioms rotatingRoots_pool_succ
end Project.EulerGridStep.Execution
