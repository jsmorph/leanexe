import Library.Numerics.Arithmetic.Gcd.Program
import Library.Numerics.Arithmetic.Gcd.Spec

namespace Library.Numerics.Arithmetic.Gcd

theorem source_zero (a : UInt64) : Library.Numerics.Arithmetic.Gcd.gcd a 0 = a := by
  rw [Library.Numerics.Arithmetic.Gcd.gcd.eq_def]
  simp

theorem source_step (a b : UInt64) (h : b ≠ 0) :
    Library.Numerics.Arithmetic.Gcd.gcd a b = Library.Numerics.Arithmetic.Gcd.gcd b (a % b) := by
  rw [Library.Numerics.Arithmetic.Gcd.gcd.eq_def]
  simp [h]

/-- Euclid's algorithm on words computes the greatest common divisor. -/
theorem gcd_eq (a b : UInt64) : Library.Numerics.Arithmetic.Gcd.gcd a b = expected (a, b) := by
  by_cases hb : b = 0
  · subst hb
    simp [source_zero, expected]
  · rw [source_step a b hb, gcd_eq b (a % b)]
    simp only [expected, UInt64.toNat_mod]
    rw [Nat.gcd_comm b.toNat (a.toNat % b.toNat), ← Nat.gcd_rec b.toNat a.toNat,
      Nat.gcd_comm b.toNat a.toNat]
termination_by b.toNat
decreasing_by
  rw [UInt64.toNat_mod]
  apply Nat.mod_lt
  apply Nat.pos_of_ne_zero
  intro hZero
  exact hb (UInt64.toNat_inj.mp (by simpa using hZero))

end Library.Numerics.Arithmetic.Gcd
