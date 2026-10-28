import Verified.TreeNodeArgs
import Verified.TreeParent
import Verified.TreeAssembleCode

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Runtime

theorem treeNode_code_eq {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (h base : Nat) (slots : List Slot) (live : Nat → Bool) :
    let ps := tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))
    let args := treeArgs words children arrays buffers
    let kept := fun k => live k || optionVarUses reuse k
    let L := fieldLive args.get kept
    (Expr.treeNode r reuse words arrays buffers children).code (pool := pool) h slots base live =
      argsCode (fun i : Fin ps.length =>
        (args.get i).code (pool := pool) h slots (base + shape.bindWidth r) (L (i.val + 1)) ++
        coerceCode h (ps.get i) ((args.get i).mode (slots.map Slot.mode)) .owned
          (base + shape.bindWidth r) ++
        storeCode h (base + 1 + i.val) (ps.get i).types) ++
      treeParentCode shape r reuse slots base live ++ shape.tagStoreCode r base ++
      treeStoreFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
        shape.fieldStart (shape.fields r) ++
      treeStoreHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
        (base + 1 + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      sealRecordCode (shape.width r) base (shape.mask r) ++ [.localGet base] := by
  let kept := fun k => live k || optionVarUses reuse k
  let L := fieldLive (treeArgs words children arrays buffers).get kept
  have hWords : ∀ i : Fin (shape.words r), L (i.val + 1) = fun k => kept k ||
      (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
      (argsAny fun j => (children j).uses k) || (argsAny fun j => (arrays j).uses k) ||
      (argsAny fun j => (buffers j).uses k) :=
    fun i => funext (treeArgs_wordLive words children arrays buffers kept i)
  have hChildren : ∀ i : Fin (shape.children r), L (shape.words r + i.val + 1) = fun k =>
      kept k || (argsAny fun j => decide (i.val < j.val) && (children j).uses k) ||
      (argsAny fun j => (arrays j).uses k) || (argsAny fun j => (buffers j).uses k) :=
    fun i => funext (treeArgs_childLive words children arrays buffers kept i)
  have hArrays : ∀ i : Fin (shape.arrays r),
      L (shape.words r + shape.children r + i.val + 1) = fun k =>
      kept k || (argsAny fun j => decide (i.val < j.val) && (arrays j).uses k) ||
      (argsAny fun j => (buffers j).uses k) :=
    fun i => funext (treeArgs_arrayLive words children arrays buffers kept i)
  have hBuffers : ∀ i : Fin (shape.buffers r),
      L (shape.words r + shape.children r + shape.arrays r + i.val + 1) = fun k =>
      kept k || (argsAny fun j => decide (i.val < j.val) && (buffers j).uses k) :=
    fun i => funext (treeArgs_bufferLive words children arrays buffers kept i)
  have hCode := Args.code_prependFn (pool := pool) (shape.words r) (shape.wordTy r) words
    (Args.prependRepeat (.tree shape) (shape.children r) children
      (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Args.prependRepeat .bytes (shape.buffers r) buffers Args.nil)))
    h (base + 1) (base + shape.bindWidth r) slots L
  have hChildCode := Args.code_prependRepeat (pool := pool)
    (.tree shape) (shape.children r) children
    (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
      (Args.prependRepeat .bytes (shape.buffers r) buffers Args.nil))
    h (base + 1 + shape.words r) (base + shape.bindWidth r) slots
    (fun j => L (shape.words r + j))
  have hArrayCode := Args.code_prependFn (pool := pool) (shape.arrays r) (shape.arrayTy r) arrays
    (Args.prependRepeat .bytes (shape.buffers r) buffers Args.nil)
    h (base + 1 + shape.words r + shape.children r) (base + shape.bindWidth r) slots
    (fun j => L (shape.words r + shape.children r + j))
  have hBufferCode := Args.code_prependRepeat (pool := pool) .bytes (shape.buffers r) buffers
    Args.nil h (base + 1 + shape.words r + shape.children r + shape.arrays r)
    (base + shape.bindWidth r) slots
    (fun j => L (shape.words r + shape.children r + shape.arrays r + j))
  simp only [Nat.add_assoc] at hCode hChildCode hArrayCode hBufferCode hChildren hArrays hBuffers
  rw [hBufferCode] at hArrayCode
  rw [hArrayCode] at hChildCode
  rw [hChildCode] at hCode
  simp only [argsCode, List.append_nil] at hCode
  dsimp only
  dsimp only [L, kept, treeArgs] at hCode hWords hChildren hArrays hBuffers ⊢
  simp only [Nat.add_assoc, List.append_assoc] at hCode ⊢
  rw [hCode]
  have hWordCoerce (i : Fin (shape.words r)) (mode : Mode) :
      coerceCode h (shape.wordTy r i) mode .owned (base + shape.bindWidth r) = [] := by
    simp only [coerceCode, TreeShape.wordTy, Ty.scalar, Bool.true_eq_false, and_false,
      ↓reduceIte]
  simp only [Nat.add_assoc, hWords, hChildren, hArrays, hBuffers, hWordCoerce, List.nil_append,
    Expr.code, Expr.usesFast_eq, Ty.types, Elem.types, storeCode, slotIndex, treeParentCode,
    recordAllocate, UInt64.ofNat_mul, sealRecordCode, List.append_assoc, TreeShape.arrayTy_types]
  cases reuse <;> rfl

end Verified
