import LeanExe.RepeatWhile
import Project.Smalltalk.Memory

namespace Project.Smalltalk.Loops

theorem go_invariant {α : Type} (P : α → Prop) (cond : α → Bool) (step : α → α)
    (preserve : ∀ s, P s → cond s = true → P (step s))
    (fuel : Nat) (s : α) (initial : P s) : P (LeanExe.repeatWhile.go cond step fuel s) := by
  induction fuel generalizing s with
  | zero => exact initial
  | succ fuel ih =>
    by_cases test : cond s = true
    · simp only [LeanExe.repeatWhile.go, test, ite_true]
      exact ih _ (preserve s initial test)
    · simp only [LeanExe.repeatWhile.go, test, ite_false]
      exact initial

theorem repeat_invariant {α : Type} (P : α → Prop) (cond : α → Bool) (step : α → α)
    (preserve : ∀ s, P s → cond s = true → P (step s))
    (fuel : UInt64) (s : α) (initial : P s) : P (LeanExe.repeatWhile fuel s cond step) :=
  go_invariant P cond step preserve fuel.toNat s initial

theorem go_stop {α : Type} (cond : α → Bool) (step : α → α) (s : α)
    (stop : cond s = false) (fuel : Nat) : LeanExe.repeatWhile.go cond step fuel s = s := by
  cases fuel <;> simp [LeanExe.repeatWhile.go, stop]

theorem go_relation {α β : Type} (R : α → β → Prop)
    (leftCond : α → Bool) (rightCond : β → Bool) (leftStep : α → α) (rightStep : β → β)
    (condition : ∀ s t, R s t → leftCond s = rightCond t)
    (advance : ∀ s t, R s t → leftCond s = true → R (leftStep s) (rightStep t))
    (fuel : Nat) (s : α) (t : β) (initial : R s t) :
    R (LeanExe.repeatWhile.go leftCond leftStep fuel s)
      (LeanExe.repeatWhile.go rightCond rightStep fuel t) := by
  induction fuel generalizing s t with
  | zero => exact initial
  | succ fuel ih =>
    have eq := condition s t initial
    by_cases test : leftCond s = true
    · simp only [LeanExe.repeatWhile.go, ← eq, test, ite_true]
      exact ih _ _ (advance s t initial test)
    · simp only [LeanExe.repeatWhile.go, ← eq, test, ite_false]
      exact initial

theorem counted_index {α : Type} (action : α → UInt64 → α) (limit : UInt64)
    (hl : limit.toNat ≤ 1048576) (fuel : Nat) (i : UInt64) (s : α)
    (room : i.toNat + fuel ≤ limit.toNat) :
    (LeanExe.repeatWhile.go (fun st : UInt64 × α => decide (st.1 < limit))
      (fun st => (st.1 + 1, action st.2 st.1)) fuel (i, s)).1.toNat = i.toNat + fuel := by
  induction fuel generalizing i s with
  | zero => simp [LeanExe.repeatWhile.go]
  | succ fuel ih =>
    have hi : i.toNat < limit.toNat := by omega
    have test : i < limit := (UInt64.lt_iff_toNat_lt).mpr hi
    have inc := Project.Smalltalk.Memory.successor_toNat (i := i) (by omega)
    simp only [LeanExe.repeatWhile.go, test, decide_true, ite_true]
    rw [ih (i + 1) (action s i) (by rw [inc]; omega), inc]
    omega

end Project.Smalltalk.Loops
