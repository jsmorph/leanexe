import Verified.FieldsArgs

namespace Verified

def treeArgs {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) :
    Args S Γ (List.replicate shape.words .word ++
      (List.replicate shape.children (.tree shape) ++ [])) :=
  Args.prependRepeat .word shape.words words
    (Args.prependRepeat (.tree shape) shape.children children .nil)

theorem treeArgs_denote {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (funs : Funs S) (env : Env Γ) (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) :
    (treeArgs words children).denote funs env =
      Env.prependRepeat .word shape.words (fun i => (words i).denote funs env)
        (Env.prependRepeat (.tree shape) shape.children
          (fun i => (children i).denote funs env) .nil) := by
  simp only [treeArgs, Args.denote_prependRepeat, Args.denote]

theorem treeArgs_forall {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (P : {t : Ty} → Nat → Expr S Γ t → Prop)
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape))
    (hWords : ∀ i, P i.val (words i)) (hChildren : ∀ i, P (shape.words + i.val) (children i)) :
    ∀ i, P i.val ((treeArgs words children).get i) := by
  apply Args.forall_get_prependRepeat P _ _ _ _ hWords
  apply Args.forall_get_prependRepeat (fun j value => P (shape.words + j) value) _ _ _ _
    hChildren
  intro i
  exact Fin.elim0 i

theorem treeArgs_any {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (P : {t : Ty} → Nat → Expr S Γ t → Bool)
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) :
    (argsAny fun i => P i.val ((treeArgs words children).get i)) =
      ((argsAny fun i => P i.val (words i)) ||
        (argsAny fun i => P (shape.words + i.val) (children i))) := by
  dsimp only [treeArgs]
  rw [Args.any_prependRepeat]
  have hChildren := Args.any_prependRepeat
    (fun {t} j (value : Expr S Γ t) => P (shape.words + j) value)
    (.tree shape) shape.children children Args.nil
  simpa only [argsAny, Bool.or_false] using
    congrArg (fun result => (argsAny fun i => P i.val (words i)) || result) hChildren

theorem treeArgs_sum {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (P : {t : Ty} → Nat → Expr S Γ t → Nat)
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) :
    (argsSum fun i => P i.val ((treeArgs words children).get i)) =
      (argsSum fun i => P i.val (words i)) +
        (argsSum fun i => P (shape.words + i.val) (children i)) := by
  dsimp only [treeArgs]
  rw [Args.sum_prependRepeat]
  have hChildren := Args.sum_prependRepeat
    (fun {t} j (value : Expr S Γ t) => P (shape.words + j) value)
    (.tree shape) shape.children children Args.nil
  simpa only [argsSum, Nat.add_zero] using
    congrArg (fun result => (argsSum fun i => P i.val (words i)) + result) hChildren

theorem treeArgs_live {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) (kept : Nat → Bool)
    (offset k : Nat) :
    fieldLive (treeArgs words children).get kept offset k =
      (kept k || (argsAny fun i => decide (offset ≤ i.val) && (words i).uses k) ||
        (argsAny fun i => decide (offset ≤ shape.words + i.val) && (children i).uses k)) := by
  rw [fieldLive, treeArgs_any (fun {t} j (value : Expr S Γ t) =>
    decide (offset ≤ j) && value.uses k) words children]
  exact (Bool.or_assoc _ _ _).symm

theorem treeArgs_wordLive {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) (kept : Nat → Bool)
    (i : Fin shape.words) (k : Nat) :
    fieldLive (treeArgs words children).get kept (i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
        (argsAny fun j => (children j).uses k)) := by
  rw [treeArgs_live]
  have hChildren : (fun j : Fin shape.children =>
      decide (i.val + 1 ≤ shape.words + j.val) && (children j).uses k) =
      fun j => (children j).uses k := by
    funext j
    have hi := i.isLt
    simp only [show i.val + 1 ≤ shape.words + j.val by omega, decide_true, Bool.true_and]
  rw [hChildren]
  simp only [Nat.add_one_le_iff]

theorem treeArgs_childLive {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape)) (kept : Nat → Bool)
    (i : Fin shape.children) (k : Nat) :
    fieldLive (treeArgs words children).get kept (shape.words + i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (children j).uses k)) := by
  rw [treeArgs_live]
  have hWords : (fun j : Fin shape.words =>
      decide (shape.words + i.val + 1 ≤ j.val) && (words j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words + i.val + 1 ≤ j.val by omega, decide_false, Bool.false_and]
  rw [hWords, argsAny_false, Bool.or_false]
  simp only [Nat.add_assoc, Nat.add_le_add_iff_left, Nat.add_one_le_iff]

end Verified
