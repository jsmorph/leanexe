import Verified.FieldsArgs
import Verified.WordCode

namespace Verified

def treeArgs {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) :
    Args S Γ (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++ [])) :=
  Args.prependFn (shape.words r) (shape.wordTy r) words
    (Args.prependRepeat (.tree shape) (shape.children r) children .nil)

theorem treeArgs_denote {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (funs : Funs S) (env : Env Γ) (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) :
    (treeArgs words children).denote funs env =
      Env.prependFn (shape.words r) (shape.wordTy r) (fun i => (words i).denote funs env)
        (Env.prependRepeat (.tree shape) (shape.children r)
          (fun i => (children i).denote funs env) .nil) := by
  simp only [treeArgs, Args.denote_prependFn, Args.denote_prependRepeat, Args.denote]

theorem treeArgs_forall {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (P : {t : Ty} → Nat → Expr S Γ t → Prop)
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (hWords : ∀ i, P i.val (words i))
    (hChildren : ∀ i, P (shape.words r + i.val) (children i)) :
    ∀ i, P i.val ((treeArgs words children).get i) := by
  apply Args.forall_get_prependFn P _ _ _ _ hWords
  apply Args.forall_get_prependRepeat (fun j value => P (shape.words r + j) value) _ _ _ _
    hChildren
  intro i
  exact Fin.elim0 i

theorem treeArgs_any {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (P : {t : Ty} → Nat → Expr S Γ t → Bool)
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) :
    (argsAny fun i => P i.val ((treeArgs words children).get i)) =
      ((argsAny fun i => P i.val (words i)) ||
        (argsAny fun i => P (shape.words r + i.val) (children i))) := by
  dsimp only [treeArgs]
  rw [Args.any_prependFn]
  have hChildren := Args.any_prependRepeat
    (fun {t} j (value : Expr S Γ t) => P (shape.words r + j) value)
    (.tree shape) (shape.children r) children Args.nil
  simpa only [argsAny, Bool.or_false] using
    congrArg (fun result => (argsAny fun i => P i.val (words i)) || result) hChildren

theorem treeArgs_sum {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (P : {t : Ty} → Nat → Expr S Γ t → Nat)
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) :
    (argsSum fun i => P i.val ((treeArgs words children).get i)) =
      (argsSum fun i => P i.val (words i)) +
        (argsSum fun i => P (shape.words r + i.val) (children i)) := by
  dsimp only [treeArgs]
  rw [Args.sum_prependFn]
  have hChildren := Args.sum_prependRepeat
    (fun {t} j (value : Expr S Γ t) => P (shape.words r + j) value)
    (.tree shape) (shape.children r) children Args.nil
  simpa only [argsSum, Nat.add_zero] using
    congrArg (fun result => (argsSum fun i => P i.val (words i)) + result) hChildren

theorem treeArgs_live {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) (kept : Nat → Bool)
    (offset k : Nat) :
    fieldLive (treeArgs words children).get kept offset k =
      (kept k || (argsAny fun i => decide (offset ≤ i.val) && (words i).uses k) ||
        (argsAny fun i => decide (offset ≤ shape.words r + i.val) && (children i).uses k)) := by
  rw [fieldLive, treeArgs_any (fun {t} j (value : Expr S Γ t) =>
    decide (offset ≤ j) && value.uses k) words children]
  exact (Bool.or_assoc _ _ _).symm

theorem treeArgs_wordLive {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) (kept : Nat → Bool)
    (i : Fin (shape.words r)) (k : Nat) :
    fieldLive (treeArgs words children).get kept (i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
        (argsAny fun j => (children j).uses k)) := by
  rw [treeArgs_live]
  have hChildren : (fun j : Fin (shape.children r) =>
      decide (i.val + 1 ≤ shape.words r + j.val) && (children j).uses k) =
      fun j => (children j).uses k := by
    funext j
    have hi := i.isLt
    simp only [show i.val + 1 ≤ shape.words r + j.val by omega, decide_true, Bool.true_and]
  rw [hChildren]
  simp only [Nat.add_one_le_iff]

theorem treeArgs_childLive {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape)) (kept : Nat → Bool)
    (i : Fin (shape.children r)) (k : Nat) :
    fieldLive (treeArgs words children).get kept (shape.words r + i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (children j).uses k)) := by
  rw [treeArgs_live]
  have hWords : (fun j : Fin (shape.words r) =>
      decide (shape.words r + i.val + 1 ≤ j.val) && (words j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + i.val + 1 ≤ j.val by omega, decide_false, Bool.false_and]
  rw [hWords, argsAny_false, Bool.or_false]
  simp only [Nat.add_assoc, Nat.add_le_add_iff_left, Nat.add_one_le_iff]


theorem tysOfFn_flatMap_types : (n : Nat) → (ts : Fin n → Ty) → (tys : Fin n → Wasm.ValueType) →
    (∀ i, (ts i).types = [tys i]) → (tysOfFn n ts).flatMap Ty.types = List.ofFn tys
  | 0, _, _, _ => rfl
  | n + 1, ts, tys, h => by
    rw [tysOfFn, List.flatMap_cons, h 0, List.ofFn_succ,
      tysOfFn_flatMap_types n (fun i => ts i.succ) (fun i => tys i.succ) (fun i => h i.succ)]
    rfl

/-- The WebAssembly types of a record's fields in a construction's locals: each word field's slot
type, then i64 for each child. -/
theorem flatMap_types_replicate_tree (shape : TreeShape) :
    (n : Nat) → (List.replicate n (Ty.tree shape)).flatMap Ty.types = List.replicate n .i64
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, flatMap_types_replicate_tree shape n]
    rfl

theorem treeArgs_types (shape : TreeShape) (r : Fin shape.records) :
    (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (Ty.tree shape) ++ [])).flatMap Ty.types =
      shape.wordTypes r ++ List.replicate (shape.children r) .i64 := by
  rw [List.append_nil, List.flatMap_append,
    tysOfFn_flatMap_types (shape.words r) (shape.wordTy r) (fun i => (shape.elem r i).slotType)
      (fun i => Elem.types_one (shape.elem r i) (shape.elem_width r i)),
    flatMap_types_replicate_tree]
  rfl

end Verified
