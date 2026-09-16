import LeanExe.KernelCheck.Sort
import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic.Omega

namespace LeanExe.KernelCheck

private theorem successor_fits (u : UInt64) (h : u ≠ 18446744073709551615) :
    u.toNat + 1 < 2 ^ 64 := by
  have hu := u.toNat_lt
  have hne : u.toNat ≠ 18446744073709551615 := by
    intro eq
    apply h
    apply UInt64.toNat.inj
    simpa using eq
  omega

/-- Acceptance is exactly the mathematical sort rule, with natural-number
succession rather than wrapping machine-word addition. This quantifies over
all input words, including the representation boundary. -/
theorem checkSort_accept_iff (u claimed : UInt64) :
    checkSort u claimed = 0 ↔ claimed.toNat = u.toNat + 1 := by
  by_cases h : u = 18446744073709551615
  · subst u
    have bound := claimed.toNat_lt
    simp [checkSort]
    omega
  · have fits := successor_fits u h
    have succNat : (u + 1).toNat = u.toNat + 1 := by
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    by_cases eq : claimed = u + 1
    · subst claimed
      simp [checkSort, h, succNat]
    · have neNat : claimed.toNat ≠ u.toNat + 1 := by
        intro equal
        apply eq
        apply UInt64.toNat.inj
        exact equal.trans succNat.symm
      simp [checkSort, h, eq, neNat]

/-- Status 2 means precisely that the successor cannot fit in UInt64. -/
theorem checkSort_overflow_iff (u claimed : UInt64) :
    checkSort u claimed = 2 ↔ 2 ^ 64 ≤ u.toNat + 1 := by
  by_cases h : u = 18446744073709551615
  · subst u
    simp [checkSort]
  · have fits := successor_fits u h
    have bound : ¬ 2 ^ 64 ≤ u.toNat + 1 := by omega
    by_cases eq : claimed = u + 1 <;> simp [checkSort, h, eq, bound]

/-- Definite rejection occurs precisely for a representable successor with
an incorrect claimed natural-number level. -/
theorem checkSort_reject_iff (u claimed : UInt64) :
    checkSort u claimed = 1 ↔
      u.toNat + 1 < 2 ^ 64 ∧ claimed.toNat ≠ u.toNat + 1 := by
  by_cases h : u = 18446744073709551615
  · subst u
    simp [checkSort]
  · have fits := successor_fits u h
    have accepts := checkSort_accept_iff u claimed
    by_cases eq : claimed = u + 1
    · have ok : checkSort u claimed = 0 := by simp [checkSort, h, eq]
      have correct := accepts.mp ok
      simp [ok, correct]
    · have wrong : claimed.toNat ≠ u.toNat + 1 := by
        intro correct
        have ok := accepts.mpr correct
        simp [checkSort, h, eq] at ok
      simp [checkSort, h, eq, fits, wrong]

end LeanExe.KernelCheck
