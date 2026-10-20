import Verified.ListFoldState
import Verified.ArgsCorrect

namespace Verified

open Wasm LeanExe.Pipeline

theorem Env.moves_borrowed (store : Store Unit) {Γ : List Ty} (ws : List Value) (env : Env Γ) :
    Env.moves store (fun _ => .borrowed) ws env = [] := by
  induction env generalizing ws with
  | nil => rfl
  | cons value env ih => simpa only [Env.moves, List.nil_append] using ih (ws.drop _)

theorem Env.argPot_eq_zero {sel : Nat → Bool} (h : ∀ i, sel i = false)
    (store : Store Unit) {Γ : List Ty} (ws : List Value) (env : Env Γ) :
    Env.argPot store sel ws env = 0 := by
  induction env generalizing sel ws with
  | nil => rfl
  | cons value env ih =>
    simp only [Env.argPot, h 0, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact ih (fun i => h (i + 1)) _

namespace ListFold

theorem paramMode_eq_borrowed (e : Elem) (captures : List Ty) :
    paramMode (params e captures) [] = fun _ => .borrowed :=
  funext (paramMode_default (params e captures))

theorem moves_eq_nil {e : Elem} {captures : List Ty} (store : Store Unit)
    (ws : List Value) (env : Env (params e captures)) :
    Env.moves store (paramMode (params e captures) []) ws env = [] := by
  rw [paramMode_eq_borrowed]
  exact Env.moves_borrowed store ws env

theorem argPot_eq_zero {e : Elem} {captures : List Ty} (store : Store Unit)
    (paid : List Bool) (ws : List Value) (env : Env (params e captures)) :
    Env.argPot store (fun i => paidAt paid i && paramMode (params e captures) [] i == .owned)
      ws env = 0 := by
  apply Env.argPot_eq_zero
  intro i
  simp only [paramMode_default]
  change (paidAt paid i && false) = false
  exact Bool.and_false _

end ListFold
end Verified
