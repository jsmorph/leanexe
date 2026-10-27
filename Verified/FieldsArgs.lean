import Verified.FieldsCompose
import Verified.FieldsOrder

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm

theorem Args.get_cons_zero {S : List Sig} {Γ ps : List Ty} {t : Ty}
    (value : Expr S Γ t) (tail : Args S Γ ps) (h : 0 < (t :: ps).length) :
    (Args.cons value tail).get ⟨0, h⟩ = value := rfl

theorem Args.get_cons_zero' {S : List Sig} {Γ ps : List Ty} {t : Ty}
    (value : Expr S Γ t) (tail : Args S Γ ps) :
    (Args.cons value tail).get 0 = value := rfl

theorem Args.get_cons_succ {S : List Sig} {Γ ps : List Ty} {t : Ty}
    (value : Expr S Γ t) (tail : Args S Γ ps) (i : Fin ps.length) :
    (Args.cons value tail).get i.succ = tail.get i := rfl

def Args.prependRepeat {S : List Sig} {Γ ps : List Ty} (t : Ty) :
    (n : Nat) → (Fin n → Expr S Γ t) → Args S Γ ps → Args S Γ (List.replicate n t ++ ps)
  | 0, _, tail => tail
  | n + 1, args, tail => .cons (args 0) (prependRepeat t n (fun i => args i.succ) tail)

def Args.denote {S : List Sig} {Γ : List Ty} (funs : Funs S) (env : Env Γ) :
    {ps : List Ty} → Args S Γ ps → Env ps
  | _, .nil => .nil
  | _, .cons value tail => .cons (value.denote funs env) (tail.denote funs env)

theorem Args.denote_eq_ofFn {S : List Sig} {Γ ps : List Ty} (funs : Funs S) (env : Env Γ)
    (args : Args S Γ ps) : args.denote funs env = Env.ofFn fun i => (args.get i).denote funs env := by
  induction args with
  | nil => rfl
  | cons value tail ih =>
    simp only [Args.denote, Env.ofFn, Args.get_cons_zero, Args.get_cons_succ, ih]

theorem Args.denote_prependRepeat {S : List Sig} {Γ ps : List Ty}
    (funs : Funs S) (env : Env Γ) (t : Ty) (n : Nat) (args : Fin n → Expr S Γ t)
    (tail : Args S Γ ps) :
    (prependRepeat t n args tail).denote funs env =
      Env.prependRepeat t n (fun i => (args i).denote funs env) (tail.denote funs env) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Args.prependRepeat, Args.denote, Env.prependRepeat, ih]

theorem Args.code_prependRepeat {S : List Sig} {Γ ps : List Ty}
    (t : Ty) (n : Nat) (args : Fin n → Expr S Γ t) (tail : Args S Γ ps)
    (h fieldBase scratch : Nat) (slots : List Slot) (L : Nat → Nat → Bool) :
    argsCode (fun i =>
      ((prependRepeat t n args tail).get i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h ((List.replicate n t ++ ps).get i)
        (((prependRepeat t n args tail).get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + i.val) ((List.replicate n t ++ ps).get i).types) =
    argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h t ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + i.val) t.types) ++
    argsCode (fun i => (tail.get i).code (pool := pool) h slots scratch (L (n + i.val + 1)) ++
      coerceCode h (ps.get i) ((tail.get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + n + i.val) (ps.get i).types) := by
  induction n generalizing fieldBase L with
  | zero =>
    simp only [Args.prependRepeat, argsCode, List.replicate_zero, Nat.zero_add, Nat.add_zero,
      List.nil_append]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, argsCode, Args.prependRepeat,
      Args.get_cons_zero, Args.get_cons_succ, List.get_eq_getElem, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.val_succ, Nat.zero_add,
      Nat.add_zero, List.append_assoc]
    have hTail := ih (fun i => args i.succ) (fieldBase + 1) (fun j => L (j + 1))
    simp only [List.get_eq_getElem, Nat.add_assoc, Nat.add_comm 1, List.append_assoc] at hTail ⊢
    rw [hTail]
    simp only [Fin.zero_eta]

theorem Args.forall_get_prependRepeat {S : List Sig} {Γ ps : List Ty}
    (P : {t : Ty} → Nat → Expr S Γ t → Prop) (t : Ty) (n : Nat)
    (args : Fin n → Expr S Γ t) (tail : Args S Γ ps)
    (hArgs : ∀ i, P i.val (args i)) (hTail : ∀ i, P (n + i.val) (tail.get i)) :
    ∀ i, P i.val ((prependRepeat t n args tail).get i) := by
  induction n generalizing P with
  | zero => simpa only [Args.prependRepeat, List.replicate_zero, List.nil_append, Nat.zero_add]
      using hTail
  | succ n ih =>
    intro i
    cases i using Fin.cases with
    | zero => simpa only [Args.prependRepeat, List.replicate_succ, List.cons_append,
        Args.get_cons_zero', List.get_cons_zero, Fin.val_zero] using hArgs 0
    | succ i =>
      have hRest := ih (P := fun k value => P (k + 1) value) (fun j => args j.succ)
        (fun j => hArgs j.succ) (fun j => by
          simpa only [Nat.add_assoc, Nat.add_comm 1] using hTail j) i
      simpa only [Args.prependRepeat, Args.get_cons_succ, Fin.val_succ] using hRest

theorem Args.sum_prependRepeat {S : List Sig} {Γ ps : List Ty}
    (P : {t : Ty} → Nat → Expr S Γ t → Nat) (t : Ty) (n : Nat)
    (args : Fin n → Expr S Γ t) (tail : Args S Γ ps) :
    (argsSum fun i => P i.val ((prependRepeat t n args tail).get i)) =
      (argsSum fun i => P i.val (args i)) + (argsSum fun i => P (n + i.val) (tail.get i)) := by
  induction n generalizing P with
  | zero => simp only [Args.prependRepeat, List.replicate_zero, List.nil_append, argsSum,
      Nat.zero_add]
  | succ n ih =>
    simp only [Args.prependRepeat, List.replicate_succ, List.cons_append, argsSum,
      Args.get_cons_zero', Args.get_cons_succ, List.get_eq_getElem,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_succ, Fin.val_zero]
    have hRest := ih (P := fun k value => P (k + 1) value) (fun j => args j.succ)
    simpa only [List.get_eq_getElem, Nat.add_assoc, Nat.add_comm 1, Fin.zero_eta] using
      congrArg (fun total => P 0 (args 0) + total) hRest

theorem Args.any_prependRepeat {S : List Sig} {Γ ps : List Ty}
    (P : {t : Ty} → Nat → Expr S Γ t → Bool) (t : Ty) (n : Nat)
    (args : Fin n → Expr S Γ t) (tail : Args S Γ ps) :
    (argsAny fun i => P i.val ((prependRepeat t n args tail).get i)) =
      ((argsAny fun i => P i.val (args i)) || (argsAny fun i => P (n + i.val) (tail.get i))) := by
  induction n generalizing P with
  | zero => simp only [Args.prependRepeat, List.replicate_zero, List.nil_append, argsAny,
      Nat.zero_add, Bool.false_or]
  | succ n ih =>
    simp only [Args.prependRepeat, List.replicate_succ, List.cons_append, argsAny,
      Args.get_cons_zero', Args.get_cons_succ, List.get_eq_getElem,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_succ, Fin.val_zero]
    have hRest := ih (P := fun k value => P (k + 1) value) (fun j => args j.succ)
    simpa only [List.get_eq_getElem, Nat.add_assoc, Nat.add_comm 1, Bool.or_assoc, Fin.zero_eta] using
      congrArg (fun any => P 0 (args 0) || any) hRest

end Verified
