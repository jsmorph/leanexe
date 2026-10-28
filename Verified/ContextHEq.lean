import Verified.BindPrefix

namespace Verified

open Wasm LeanExe.Pipeline

theorem Env.cons_heq {Γ Δ : List Ty} {t : Ty} {first : Env Γ} {second : Env Δ}
    (hΓ : Γ = Δ) (h : HEq first second) (v : t.denote) :
    HEq (Env.cons v first) (Env.cons v second) := by
  cases hΓ
  cases h
  rfl

theorem Env.repeat_heq {Γ Δ : List Ty} {first : Env Γ} {second : Env Δ}
    (hΓ : Γ = Δ) (h : HEq first second) (t : Ty) (n : Nat) (values : Fin n → t.denote) :
    HEq (Env.prependRepeat t n values first) (Env.prependRepeat t n values second) := by
  cases hΓ
  cases h
  rfl

theorem Env.repeat_append {Γ Δ : List Ty} (first : Env Γ) (second : Env Δ)
    (t : Ty) : ∀ n (values : Fin n → t.denote),
    HEq ((Env.prependRepeat t n values first).append second)
      (Env.prependRepeat t n values (first.append second))
  | 0, _ => HEq.rfl
  | n + 1, values =>
    Env.cons_heq (List.append_assoc (List.replicate n t) Γ Δ)
      (Env.repeat_append first second t n (fun i => values i.succ)) (values 0)

theorem Env.fn_heq {Γ Δ : List Ty} {first : Env Γ} {second : Env Δ}
    (hΓ : Γ = Δ) (h : HEq first second) (n : Nat) (ts : Fin n → Ty)
    (values : (i : Fin n) → (ts i).denote) :
    HEq (Env.prependFn n ts values first) (Env.prependFn n ts values second) := by
  cases hΓ
  cases h
  rfl

theorem Env.fn_append {Γ Δ : List Ty} (first : Env Γ) (second : Env Δ) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote),
    HEq ((Env.prependFn n ts values first).append second)
      (Env.prependFn n ts values (first.append second))
  | 0, _, _ => HEq.rfl
  | n + 1, ts, values =>
    Env.cons_heq (List.append_assoc (tysOfFn n fun i => ts i.succ) Γ Δ)
      (Env.fn_append first second n (fun i => ts i.succ) (fun i => values i.succ)) (values 0)

theorem Holds.ofHEq {Γ Δ : List Ty} {first : Env Γ} {second : Env Δ}
    (hΓ : Γ = Δ) (h : HEq first second) {slots : List Slot} {live : Nat → Bool}
    {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hVars : Holds first slots live base heap store s) :
    Holds second slots live base heap store s := by
  cases hΓ
  cases h
  exact hVars

theorem After.ofHEq {Γ Δ : List Ty} {first : Env Γ} {second : Env Δ}
    (hΓ : Γ = Δ) (h : HEq first second) {slots : List Slot} {L0 live : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals}
    {t : Ty} {mode : Mode} {v : t.denote} {ws : List Value}
    (hAfter : After first slots L0 live base heap store s t mode v heap' store' s' ws) :
    After second slots L0 live base heap store s t mode v heap' store' s' ws := by
  cases hΓ
  cases h
  exact hAfter

end Verified
