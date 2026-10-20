import Verified.TreeNodeArgs
import Verified.TreeParent

namespace Verified

theorem treeNode_entryLive {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (reuse : Option (Var Γ (.treeHeader shape)))
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) (live : Nat → Bool) :
    fieldLive (treeArgs words children).get (fun k => live k || optionVarUses reuse k) 0 =
      fun k => live k || (Expr.treeNode reuse words children).uses k := by
  funext k
  rw [fieldLive_zero, treeArgs_any (fun {t} _ (e : Expr S Γ t) => e.uses k) words children]
  simp only [Expr.uses, Bool.or_assoc]

theorem treeNode_fieldCost {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (reuse : Option (Var Γ (.treeHeader shape)))
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) (funs : Funs S)
    (flags : Flags S) (bounds : Bounds S) (slots : List Slot) (paid : List Bool)
    (live : Nat → Bool) (env : Env Γ) :
    let args := treeArgs words children
    let L := fieldLive args.get (fun k => live k || optionVarUses reuse k)
    argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args.get env) +
      treeParentCost shape reuse slots live =
        (Expr.treeNode reuse words children).allocs funs flags bounds (slots.map Slot.mode)
          paid live env := by
  let kept := fun k => live k || optionVarUses reuse k
  let L := fieldLive (treeArgs words children).get kept
  let P : {t : Ty} → Nat → Expr S Γ t → Nat := fun {t} i e =>
    e.allocs funs flags bounds (slots.map Slot.mode) paid (L (i + 1)) env +
      coerceCost t (e.mode (slots.map Slot.mode)) .owned (e.denote funs env)
  have hWords : ∀ i : Fin shape.words, L (i.val + 1) = fun k => kept k ||
      (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
      (argsAny fun j => (children j).uses k) :=
    fun i => funext (treeArgs_wordLive words children kept i)
  have hChildren : ∀ i : Fin shape.children, L (shape.words + i.val + 1) = fun k => kept k ||
      (argsAny fun j => decide (i.val < j.val) && (children j).uses k) :=
    fun i => funext (treeArgs_childLive words children kept i)
  have hWordCost (i : Fin shape.words) : P i.val (words i) =
      (words i).allocs funs flags bounds (slots.map Slot.mode) paid
        (fun k => kept k || (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
          (argsAny fun j => (children j).uses k)) env := by
    dsimp only [P]
    rw [hWords i]
    simp only [coerceCost, Ty.copyCost, ite_self, Nat.add_zero]
  have hChildCost (i : Fin shape.children) : P (shape.words + i.val) (children i) =
      (children i).allocs funs flags bounds (slots.map Slot.mode) paid
        (fun k => kept k || (argsAny fun j => decide (i.val < j.val) && (children j).uses k)) env +
      coerceCost (.tree shape) ((children i).mode (slots.map Slot.mode)) .owned
        ((children i).denote funs env) := by
    dsimp only [P]
    rw [hChildren i]
  change (argsSum fun i => P i.val ((treeArgs words children).get i)) + _ = _
  rw [treeArgs_sum P words children]
  simp only [hWordCost, hChildCost, Expr.allocs, treeParentCost, modeAt, Slot.modes_getD]
  cases reuse <;> rfl

end Verified
