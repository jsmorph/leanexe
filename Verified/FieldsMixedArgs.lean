import Verified.FieldsArgs
import Verified.FieldsMixed

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm

theorem Ty.normalizeCode_bytes (loc : Nat) :
    Ty.normalizeCode .bytes loc = Bytes.normalizeCode loc (loc + 1) := rfl

/-- The code of arguments of width 1 with nothing after their stores, before `tail`, as the
arguments of `fieldsMixed_spec`. -/
theorem Args.code_prependFn_mixed {S : List Sig} {Γ ps : List Ty}
    (n : Nat) (ts : Fin n → Ty) (args : (i : Fin n) → Expr S Γ (ts i)) (tail : Args S Γ ps)
    (hWidth : ∀ i, (ts i).width = 1) (hNorm : ∀ i loc, (ts i).normalizeCode loc = [])
    (h fieldBase scratch : Nat) (slots : List Slot) (L : Nat → Nat → Bool) :
    argsCode (fun i =>
      ((prependFn n ts args tail).get i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h ((tysOfFn n ts ++ ps).get i)
        (((prependFn n ts args tail).get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + fieldOffset (tysOfFn n ts ++ ps) i.val)
        ((tysOfFn n ts ++ ps).get i).types ++
      ((tysOfFn n ts ++ ps).get i).normalizeCode
        (fieldBase + fieldOffset (tysOfFn n ts ++ ps) i.val)) =
    argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h (ts i) ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + i.val) (ts i).types) ++
    argsCode (fun i => (tail.get i).code (pool := pool) h slots scratch (L (n + i.val + 1)) ++
      coerceCode h (ps.get i) ((tail.get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + n + fieldOffset ps i.val) (ps.get i).types ++
      (ps.get i).normalizeCode (fieldBase + n + fieldOffset ps i.val)) := by
  induction n generalizing fieldBase L with
  | zero =>
    simp only [Args.prependFn, argsCode, tysOfFn, Nat.zero_add, Nat.add_zero, List.nil_append]
  | succ n ih =>
    simp only [tysOfFn, List.cons_append, argsCode, Args.prependFn,
      Args.get_cons_zero, Args.get_cons_succ, List.get_eq_getElem, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.val_succ, Nat.zero_add, fieldOffset_zero, fieldOffset_succ,
      hWidth, hNorm, Nat.add_zero, List.append_nil, List.append_assoc]
    have hTail := ih (fun i => ts i.succ) (fun i => args i.succ) (fun i => hWidth i.succ)
      (fun i => hNorm i.succ) (fieldBase + 1) (fun j => L (j + 1))
    simp only [List.get_eq_getElem, Nat.add_assoc, Nat.add_comm 1, List.append_assoc] at hTail ⊢
    rw [hTail]
    simp only [Fin.zero_eta]

/-- The code of `n` arguments of type `t`, of width 1 with nothing after their stores, before
`tail`, as the arguments of `fieldsMixed_spec`. -/
theorem Args.code_prependRepeat_mixed {S : List Sig} {Γ ps : List Ty}
    (t : Ty) (n : Nat) (args : Fin n → Expr S Γ t) (tail : Args S Γ ps)
    (hWidth : t.width = 1) (hNorm : ∀ loc, t.normalizeCode loc = [])
    (h fieldBase scratch : Nat) (slots : List Slot) (L : Nat → Nat → Bool) :
    argsCode (fun i =>
      ((prependRepeat t n args tail).get i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h ((List.replicate n t ++ ps).get i)
        (((prependRepeat t n args tail).get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + fieldOffset (List.replicate n t ++ ps) i.val)
        ((List.replicate n t ++ ps).get i).types ++
      ((List.replicate n t ++ ps).get i).normalizeCode
        (fieldBase + fieldOffset (List.replicate n t ++ ps) i.val)) =
    argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h t ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + i.val) t.types) ++
    argsCode (fun i => (tail.get i).code (pool := pool) h slots scratch (L (n + i.val + 1)) ++
      coerceCode h (ps.get i) ((tail.get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + n + fieldOffset ps i.val) (ps.get i).types ++
      (ps.get i).normalizeCode (fieldBase + n + fieldOffset ps i.val)) := by
  induction n generalizing fieldBase L with
  | zero =>
    simp only [Args.prependRepeat, argsCode, List.replicate_zero, Nat.zero_add, Nat.add_zero,
      List.nil_append]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, argsCode, Args.prependRepeat,
      Args.get_cons_zero, Args.get_cons_succ, List.get_eq_getElem, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.val_succ, Nat.zero_add, fieldOffset_zero, fieldOffset_succ,
      hWidth, hNorm, Nat.add_zero, List.append_nil, List.append_assoc]
    have hTail := ih (fun i => args i.succ) (fieldBase + 1) (fun j => L (j + 1))
    simp only [List.get_eq_getElem, Nat.add_assoc, Nat.add_comm 1, List.append_assoc] at hTail ⊢
    rw [hTail]
    simp only [Fin.zero_eta]

/-- The code of `n` buffer arguments before `tail`, as the arguments of `fieldsMixed_spec`: each
stored in two locals and normalized. -/
theorem Args.code_prependBytes_mixed {S : List Sig} {Γ ps : List Ty}
    (n : Nat) (args : Fin n → Expr S Γ .bytes) (tail : Args S Γ ps)
    (h fieldBase scratch : Nat) (slots : List Slot) (L : Nat → Nat → Bool) :
    argsCode (fun i =>
      ((prependRepeat Ty.bytes n args tail).get i).code (pool := pool) h slots scratch
        (L (i.val + 1)) ++
      coerceCode h ((List.replicate n Ty.bytes ++ ps).get i)
        (((prependRepeat Ty.bytes n args tail).get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + fieldOffset (List.replicate n Ty.bytes ++ ps) i.val)
        ((List.replicate n Ty.bytes ++ ps).get i).types ++
      ((List.replicate n Ty.bytes ++ ps).get i).normalizeCode
        (fieldBase + fieldOffset (List.replicate n Ty.bytes ++ ps) i.val)) =
    argsCode (fun i => (args i).code (pool := pool) h slots scratch (L (i.val + 1)) ++
      coerceCode h Ty.bytes ((args i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + 2 * i.val) Ty.bytes.types ++
      Bytes.normalizeCode (fieldBase + 2 * i.val) (fieldBase + 2 * i.val + 1)) ++
    argsCode (fun i => (tail.get i).code (pool := pool) h slots scratch (L (n + i.val + 1)) ++
      coerceCode h (ps.get i) ((tail.get i).mode (slots.map Slot.mode)) .owned scratch ++
      storeCode h (fieldBase + 2 * n + fieldOffset ps i.val) (ps.get i).types ++
      (ps.get i).normalizeCode (fieldBase + 2 * n + fieldOffset ps i.val)) := by
  induction n generalizing fieldBase L with
  | zero =>
    simp only [Args.prependRepeat, argsCode, List.replicate_zero, Nat.zero_add, Nat.add_zero,
      Nat.mul_zero, List.nil_append]
  | succ n ih =>
    have hWidth : Ty.bytes.width = 2 := rfl
    simp only [List.replicate_succ, List.cons_append, argsCode, Args.prependRepeat,
      Args.get_cons_zero, Args.get_cons_succ, List.get_eq_getElem, List.getElem_cons_zero,
      List.getElem_cons_succ, Fin.val_succ, Nat.zero_add, fieldOffset_zero, fieldOffset_succ,
      hWidth, Ty.normalizeCode_bytes, Nat.add_zero, Nat.mul_zero, List.append_assoc]
    have hTail := ih (fun i => args i.succ) (fieldBase + 2) (fun j => L (j + 1))
    have hIndex : ∀ k : Nat, fieldBase + 2 + 2 * k = fieldBase + 2 * (k + 1) := fun k => by
      omega
    have hEnd : fieldBase + 2 + 2 * n = fieldBase + 2 * (n + 1) := hIndex n
    simp only [hIndex, List.get_eq_getElem, List.append_assoc] at hTail
    simp only [Nat.add_assoc, Nat.add_comm 1] at hTail ⊢
    rw [hTail]
    simp only [Fin.zero_eta]

#print axioms Args.code_prependFn_mixed
#print axioms Args.code_prependRepeat_mixed
#print axioms Args.code_prependBytes_mixed

end Verified
