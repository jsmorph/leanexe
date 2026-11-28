module

public import LeanExe.Dialect.Lemmas

@[expose] public section

/-!
Tests of `LeanExe.Dialect.repeatWhile_induction` and `LeanExe.Dialect.repeatWhile_induction_stop`.
`countDown` counts a word down to 0 with `LeanExe.repeatWhile` and counts the steps in a second
component.  The fuel `n + 1` exceeds the measure, the first component, so the loop ends with the
first component 0, and the invariant that the two components sum to `n` gives the count `n`.
-/

namespace TestSupport.Dialect.RepeatWhile

/-- Counts `n` down to 0 with at most `n + 1` steps, and counts the steps. -/
def countDown (n : UInt64) : UInt64 × Nat :=
  LeanExe.repeatWhile (n + 1) (n, 0) (fun s => s.1 != 0) fun s => (s.1 - 1, s.2 + 1)

/-- A step of `countDown` under its condition lowers the first component by one. -/
theorem countDown_step (s : UInt64 × Nat) (hc : (s.1 != 0) = true) :
    (s.1 - 1).toNat + 1 = s.1.toNat := by
  have hne : s.1 ≠ 0 := by simpa using hc
  have h1 : 1 ≤ s.1.toNat := by
    rcases Nat.eq_zero_or_pos s.1.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hne
    · exact h0
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using h1))]
  simp only [UInt64.toNat_one]
  omega

/-- `countDown n` ends at 0 after `n` steps for `n < 2 ^ 63`. -/
theorem countDown_spec (n : UInt64) (h : n.toNat < 2 ^ 63) : countDown n = (0, n.toNat) := by
  have hfuel : (n + 1).toNat = n.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hsum, hstop⟩ := LeanExe.Dialect.repeatWhile_induction_stop (fuel := n + 1)
    (init := (n, (0 : Nat))) (cond := fun s : UInt64 × Nat => s.1 != 0)
    (step := fun s => (s.1 - 1, s.2 + 1)) (fun s => s.1.toNat + s.2 = n.toNat)
    (fun s => s.1.toNat) rfl (by show n.toNat ≤ (n + 1).toNat; omega) fun s hs hc => by
      have := countDown_step s hc
      simp only at hs ⊢
      omega
  change (countDown n).1.toNat + (countDown n).2 = n.toNat at hsum
  change ((countDown n).1 != 0) = false at hstop
  have h0 : (countDown n).1 = 0 := by simpa using hstop
  rw [h0] at hsum
  exact Prod.ext h0 (by simpa using hsum)

/-- `repeatWhile_induction` keeps the sum of the two components of `countDown`, so the count of
steps is at most `n`. -/
theorem countDown_count_le (n : UInt64) : (countDown n).2 ≤ n.toNat := by
  have hsum := LeanExe.Dialect.repeatWhile_induction (fuel := n + 1) (init := (n, (0 : Nat)))
    (cond := fun s : UInt64 × Nat => s.1 != 0) (step := fun s => (s.1 - 1, s.2 + 1))
    (fun s => s.1.toNat + s.2 = n.toNat) rfl fun s hs hc => by
      have := countDown_step s hc
      simp only at hs ⊢
      omega
  change (countDown n).1.toNat + (countDown n).2 = n.toNat at hsum
  omega

#print axioms LeanExe.Dialect.repeatWhile_induction
#print axioms LeanExe.Dialect.repeatWhile_induction_stop
#print axioms countDown_spec
#print axioms countDown_count_le

end TestSupport.Dialect.RepeatWhile
