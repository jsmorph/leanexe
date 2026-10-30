import Examples.RunningMax.Proof
import Verified.Call
import Verified.Reflect.Command

/-! The verified compiler's module of `compute`.  `compute_callSpec` composes the generated
`compiled.compute.trapFree` with `compute_eq`: from a ready store with room for the generated bound,
the export `compute` returns the words of `expected` without a trap.  `compute_bound` closes that
bound to `80 * xs.size + 72` bytes. -/

namespace Examples.RunningMax

verified_compile compiled := [compute]

/-- A charge of `c` bytes at each step of a word-counted fold, from `a` bytes, adds `c` bytes for
each of the `n` steps. -/
theorem fold_charge_const {β : Type} (c : Nat) :
    ∀ (n : Nat) (g : (k : Nat) → k < n → β → β) (a : Nat) (s : β),
      (Nat.fold n (fun k hk (state : Nat × β) => (state.1 + c, g k hk state.2)) (a, s)).1 =
        a + c * n
  | 0, _, a, _ => by simp
  | n + 1, g, a, s => by
    simp only [Nat.fold_succ]
    rw [fold_charge_const c n (fun k hk => g k (Nat.lt_add_one_of_lt hk)) a s, Nat.mul_succ,
      Nat.add_assoc]

/-- A fold whose every step is charged `c` bytes costs `c` bytes for each of its steps. -/
theorem foldCost_const {α β : Type} (xs : Array α) (init : β) (step : β → α → β) (c : Nat) :
    Verified.foldCost xs init step (fun _ _ _ => c) = c * xs.size.toUInt64.toNat := by
  have h := fold_charge_const c xs.size.toUInt64.toNat
    (fun k hk s => step s (xs[k]'(hk.trans_le (by exact Nat.mod_le _ _)))) 0 init
  rw [Nat.zero_add] at h
  exact h

/-- `compute` charges the empty result's block of 56 bytes, its credit of 16 bytes, and 80 bytes
for each push: at most `80 * xs.size + 72` bytes. -/
theorem compute_bound (xs : Array UInt64) : compiled.compute.bound xs ≤ 80 * xs.size + 72 := by
  have hn : xs.size.toUInt64.toNat ≤ xs.size := by exact Nat.mod_le _ _
  rw [compiled.compute.bound_eq]
  refine (min_le_right _ _).trans ?_
  rw [foldCost_const, Verified.blockCost_eq, Verified.paidGrowCost_eq]
  simp only [Verified.creditCost, Array.size_empty, UInt64.toNat_zero]
  omega

/-- `Verified.CallSpec` for function 2 and `expected`, with the generated bound as the room: from a
ready store in which `top` can rise by `compiled.compute.bound xs` bytes, the call with the
borrowed array `xs` returns an owned array that holds `expected xs`, leaves a ready store, and
raises `top` by at most that bound. -/
theorem compute_callSpec :
    Verified.CallSpec compiled.module compiled.tables 2 expected compiled.compute.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.compute.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h) fun _ _ _ xs _ => compute_eq xs

#print axioms compute_eq
#print axioms compute_bound
#print axioms compute_callSpec

end Examples.RunningMax
