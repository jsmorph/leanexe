import Verified.TreeNodeArgs
import Verified.TreeParent

namespace Verified

theorem treeNode_entryLive {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) (live : Nat → Bool) :
    fieldLive (treeArgs words children arrays buffers).get
        (fun k => live k || optionVarUses reuse k) 0 =
      fun k => live k || (Expr.treeNode r reuse words arrays buffers children).uses k := by
  funext k
  rw [fieldLive_zero, treeArgs_any (fun {t} _ (e : Expr S Γ t) => e.uses k) words children
    arrays buffers]
  simp only [Expr.uses, Bool.or_assoc]

theorem treeNode_fieldCost {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) (funs : Funs S)
    (flags : Flags S) (bounds : Bounds S) (slots : List Slot) (paid : List Bool)
    (live : Nat → Bool) (env : Env Γ) :
    let args := treeArgs words children arrays buffers
    let L := fieldLive args.get (fun k => live k || optionVarUses reuse k)
    argsSum (fieldCost funs flags bounds (slots.map Slot.mode) paid L args.get env) +
      treeParentCost shape r reuse slots live =
        (Expr.treeNode r reuse words arrays buffers children).allocs funs flags bounds
          (slots.map Slot.mode) paid live env := by
  let kept := fun k => live k || optionVarUses reuse k
  let L := fieldLive (treeArgs words children arrays buffers).get kept
  let P : {t : Ty} → Nat → Expr S Γ t → Nat := fun {t} i e =>
    e.allocs funs flags bounds (slots.map Slot.mode) paid (L (i + 1)) env +
      coerceCost t (e.mode (slots.map Slot.mode)) .owned (e.denote funs env)
  have hWordCost (i : Fin (shape.words r)) : P i.val (words i) =
      (words i).allocs funs flags bounds (slots.map Slot.mode) paid
        (fun k => kept k || (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
          (argsAny fun j => (children j).uses k) || (argsAny fun j => (arrays j).uses k) ||
          (argsAny fun j => (buffers j).uses k)) env := by
    dsimp only [P]
    rw [show L (i.val + 1) = _ from funext (treeArgs_wordLive words children arrays buffers kept i)]
    simp only [coerceCost, TreeShape.wordTy, Ty.copyCost, ite_self, Nat.add_zero]
  have hChildCost (i : Fin (shape.children r)) : P (shape.words r + i.val) (children i) =
      (children i).allocs funs flags bounds (slots.map Slot.mode) paid
        (fun k => kept k || (argsAny fun j => decide (i.val < j.val) && (children j).uses k) ||
          (argsAny fun j => (arrays j).uses k) || (argsAny fun j => (buffers j).uses k)) env +
      coerceCost (.tree shape) ((children i).mode (slots.map Slot.mode)) .owned
        ((children i).denote funs env) := by
    dsimp only [P]
    rw [show L (shape.words r + i.val + 1) = _ from
      funext (treeArgs_childLive words children arrays buffers kept i)]
  have hArrayCost (i : Fin (shape.arrays r)) :
      P (shape.words r + shape.children r + i.val) (arrays i) =
      (arrays i).allocs funs flags bounds (slots.map Slot.mode) paid
        (fun k => kept k || (argsAny fun j => decide (i.val < j.val) && (arrays j).uses k) ||
          (argsAny fun j => (buffers j).uses k)) env +
      coerceCost (shape.arrayTy r i) ((arrays i).mode (slots.map Slot.mode)) .owned
        ((arrays i).denote funs env) := by
    dsimp only [P]
    rw [show L (shape.words r + shape.children r + i.val + 1) = _ from
      funext (treeArgs_arrayLive words children arrays buffers kept i)]
  have hBufferCost (i : Fin (shape.buffers r)) :
      P (shape.words r + shape.children r + shape.arrays r + i.val) (buffers i) =
      (buffers i).allocs funs flags bounds (slots.map Slot.mode) paid
        (fun k => kept k || (argsAny fun j => decide (i.val < j.val) && (buffers j).uses k)) env +
      coerceCost .bytes ((buffers i).mode (slots.map Slot.mode)) .owned
        ((buffers i).denote funs env) := by
    dsimp only [P]
    rw [show L (shape.words r + shape.children r + shape.arrays r + i.val + 1) = _ from
      funext (treeArgs_bufferLive words children arrays buffers kept i)]
  change (argsSum fun i => P i.val ((treeArgs words children arrays buffers).get i)) + _ = _
  rw [treeArgs_sum P words children arrays buffers]
  simp only [hWordCost, hChildCost, hArrayCost, hBufferCost, Expr.allocs, treeParentCost, modeAt,
    Slot.modes_getD]
  cases reuse <;> rfl

end Verified
