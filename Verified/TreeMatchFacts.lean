import Verified.TreeMatchPotential
import Verified.OwnedExpr
import Verified.ExprSpec

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

theorem TreeShape.slots_modes_full (shape : TreeShape) (r : Fin shape.records) (base : Nat)
    (mode : Mode) (slots : List Slot) :
    (shape.slots r base mode slots).map Slot.mode = shape.modes r mode (slots.map Slot.mode) := by
  rw [shape.slots_append r, List.map_append, shape.slots_modes r]
  simp only [TreeShape.modes, List.cons_append, List.append_assoc, List.append_nil]

theorem Mode.node.zero_iff {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {mode : Mode} {p : UInt64} {value : Tree shape}
    (h : mode.node heap store p value.toNode) : p = 0 ↔ ∃ hn, value = .nil hn := by
  cases value with
  | nil hn => exact ⟨fun _ => ⟨hn, rfl⟩, fun _ => h.borrow⟩
  | node r words arrays buffers children =>
    have hp := h.borrow.1.nonzero
    exact ⟨fun hz => False.elim (hp hz), fun ⟨_, he⟩ => by cases he⟩

theorem treeCase_entryLive {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t) (live : Nat → Bool) :
    (fun i => live i || (Expr.treeCase x empty nodes).uses i) =
      (fun i => live i || decide (i = x.index) ||
        (if h : shape.hasNull = true then (empty h).uses i else false) ||
        argsAny fun r => (nodes r).uses (i + shape.bindCount r)) := by
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
    {r : Fin shape.records}
    (node : Expr S (shape.context r Γ) t) (live : Nat → Bool) :
    (fun i => (decide (i < shape.bindCount r) ||
      shift (shape.bindCount r) (fun k => live k || node.uses (k + shape.bindCount r)) i) &&
      !(decide (i < shape.bindCount r) && !node.uses i)) =
      (fun i => shift (shape.bindCount r) live i || node.uses i) := by
  funext i
  by_cases hi : i < shape.bindCount r
  · simp [shift, hi]
  · simp [shift, hi, Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

theorem treeCase_releaseFields {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {r : Fin shape.records}
    (node : Expr S (shape.context r Γ) t) (live : Nat → Bool) :
    (fun i => (decide (i < shape.bindCount r) ||
      shift (shape.bindCount r) (fun k => live k || node.uses (k + shape.bindCount r)) i) &&
      !(shift (shape.bindCount r) live i || node.uses i)) =
      (fun i => decide (i < shape.bindCount r) && !node.uses i) := by
  funext i
  by_cases hi : i < shape.bindCount r
  · simp [shift, hi]
  · cases hl : live (i - shape.bindCount r) <;> cases hn : node.uses i <;>
      simp [shift, hi, Nat.sub_add_cancel (Nat.le_of_not_gt hi), hl, hn]

theorem treeCase_fieldsLive {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {r : Fin shape.records}
    (node : Expr S (shape.context r Γ) t) (live : Nat → Bool) :
    ∀ i, (shift (shape.bindCount r) live i || node.uses i) = true →
      (decide (i < shape.bindCount r) ||
        shift (shape.bindCount r) (fun k => live k || node.uses (k + shape.bindCount r)) i) =
          true := by
  intro i hx
  by_cases hi : i < shape.bindCount r
  · simp [hi]
  · simpa [shift, hi, Nat.sub_add_cancel (Nat.le_of_not_gt hi)] using hx

end Verified
