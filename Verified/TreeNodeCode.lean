import Verified.TreeNodeArgs
import Verified.TreeParent
import Verified.TreeAssembleCode

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Runtime

theorem treeNode_code_eq {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (reuse : Option (Var Γ (.treeHeader shape)))
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape))
    (h base : Nat) (slots : List Slot) (live : Nat → Bool) :
    let ps := List.replicate shape.words .word ++
      (List.replicate shape.children (.tree shape) ++ [])
    let args := treeArgs words children
    let kept := fun k => live k || optionVarUses reuse k
    let L := fieldLive args.get kept
    (Expr.treeNode reuse words children).code (pool := pool) h slots base live =
      argsCode (fun i : Fin ps.length =>
        (args.get i).code (pool := pool) h slots (base + shape.bindCount) (L (i.val + 1)) ++
        coerceCode h (ps.get i) ((args.get i).mode (slots.map Slot.mode)) .owned
          (base + shape.bindCount) ++
        storeCode h (base + 1 + i.val) (ps.get i).types) ++
      treeParentCode shape reuse slots base live ++
      treeStoreFields base (base + 1) (base + 1 + shape.words) 0 shape.fields ++
      sealRecordCode shape base shape.mask ++ [.localGet base] := by
  let kept := fun k => live k || optionVarUses reuse k
  let L := fieldLive (treeArgs words children).get kept
  have hWords : ∀ i : Fin shape.words, L (i.val + 1) = fun k => kept k ||
      (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
      (argsAny fun j => (children j).uses k) :=
    fun i => funext (treeArgs_wordLive words children kept i)
  have hChildren : ∀ i : Fin shape.children, L (shape.words + i.val + 1) = fun k => kept k ||
      (argsAny fun j => decide (i.val < j.val) && (children j).uses k) :=
    fun i => funext (treeArgs_childLive words children kept i)
  have hCode := Args.code_prependRepeat (pool := pool) .word shape.words words
    (Args.prependRepeat (.tree shape) shape.children children Args.nil)
    h (base + 1) (base + shape.bindCount) slots L
  have hChildCode := Args.code_prependRepeat (pool := pool)
    (.tree shape) shape.children children Args.nil
    h (base + 1 + shape.words) (base + shape.bindCount) slots
    (fun j => L (shape.words + j))
  simp only [Nat.add_assoc] at hCode hChildCode hChildren
  rw [hChildCode] at hCode
  simp only [argsCode, List.append_nil] at hCode
  dsimp only
  dsimp only [L, kept, treeArgs] at hCode hWords hChildren ⊢
  simp only [Nat.add_assoc, List.append_assoc] at hCode ⊢
  rw [hCode]
  have hWordCoerce (mode : Mode) : coerceCode h .word mode .owned (base + shape.bindCount) = [] := by
    simp only [coerceCode, Ty.scalar, Bool.true_eq_false, and_false, ↓reduceIte]
  simp only [Nat.add_assoc, hWords, hChildren, hWordCoerce, List.nil_append,
    Expr.code, Expr.usesFast_eq, Ty.types, Elem.types, storeCode, slotIndex, treeParentCode,
    treeCopyAllocate, UInt64.ofNat_mul, sealRecordCode, List.append_assoc]
  cases reuse <;> rfl

end Verified
