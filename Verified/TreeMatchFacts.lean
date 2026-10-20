import Verified.TreeMatchPotential
import Verified.VarCorrect
import Verified.OwnedExpr

namespace Verified

open Wasm LeanExe.Pipeline

theorem nat_beq_decide (i j : Nat) : (i == j) = decide (i = j) := by
  by_cases h : i = j
  · simp [h]
  · have hn : (i == j) = false := by
      cases hb : i == j
      · rfl
      · exact False.elim (h (beq_iff_eq.mp hb))
    simp [h, hn]

theorem TreeShape.slots_modes_full (shape : TreeShape) (base : Nat) (mode : Mode)
    (slots : List Slot) :
    (shape.slots base mode slots).map Slot.mode = shape.modes mode (slots.map Slot.mode) := by
  rw [shape.slots_append, List.map_append, shape.slots_modes]
  simp [TreeShape.modes, List.append_assoc]

theorem Mode.node.zero_iff {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {mode : Mode} {p : UInt64} {value : Tree shape}
    (h : mode.node heap store p value.toNode) : p = 0 ↔ value = .nil := by
  cases value with
  | nil => exact ⟨fun _ => rfl, fun _ => h.borrow⟩
  | node words children =>
    have hn := h.borrow.1.nonzero
    exact ⟨fun hz => False.elim (hn hz), nofun⟩

theorem treeCase_entryLive {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    (x : Var Γ (.tree shape)) (empty : Expr S Γ t) (node : Expr S (shape.context Γ) t)
    (live : Nat → Bool) :
    (fun i => live i || (Expr.treeCase x empty node).uses i) =
      (fun i => live i || decide (i = x.index) || empty.uses i || node.uses (i + shape.bindCount)) := by
  funext i
  simp only [Expr.uses]
  by_cases hx : i = x.index
  · simp [hx]
  · have hne : (i == x.index) = false := by
      cases h : i == x.index
      · rfl
      · exact False.elim (hx (beq_iff_eq.mp h))
    simp [hx, hne, Bool.or_assoc]

theorem treeCase_releasedLive {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    (node : Expr S (shape.context Γ) t) (live : Nat → Bool) :
    (fun i => (decide (i < shape.bindCount) ||
      shift shape.bindCount (fun k => live k || node.uses (k + shape.bindCount)) i) &&
      !(decide (i < shape.bindCount) && !node.uses i)) =
      (fun i => shift shape.bindCount live i || node.uses i) := by
  funext i
  by_cases hi : i < shape.bindCount
  · simp [shift, hi]
  · simp [shift, hi, Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

theorem treeCase_releaseFields {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    (node : Expr S (shape.context Γ) t) (live : Nat → Bool) :
    (fun i => (decide (i < shape.bindCount) ||
      shift shape.bindCount (fun k => live k || node.uses (k + shape.bindCount)) i) &&
      !(shift shape.bindCount live i || node.uses i)) =
      (fun i => decide (i < shape.bindCount) && !node.uses i) := by
  funext i
  by_cases hi : i < shape.bindCount
  · simp [shift, hi]
  · cases hl : live (i - shape.bindCount) <;> cases hn : node.uses i <;>
      simp [shift, hi, Nat.sub_add_cancel (Nat.le_of_not_gt hi), hl, hn]

theorem treeCase_fieldsLive {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    (node : Expr S (shape.context Γ) t) (live : Nat → Bool) :
    ∀ i, (shift shape.bindCount live i || node.uses i) = true →
      (decide (i < shape.bindCount) ||
        shift shape.bindCount (fun k => live k || node.uses (k + shape.bindCount)) i) = true := by
  intro i hx
  by_cases hi : i < shape.bindCount
  · simp [hi]
  · simpa [shift, hi, Nat.sub_add_cancel (Nat.le_of_not_gt hi)] using hx

end Verified
