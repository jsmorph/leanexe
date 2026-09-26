import LeanExe.Examples.Beck
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Project.Beck.Arithmetic

open LeanExe.Examples.Beck

theorem twice_remainder_lt (a b : ℕ) (positive : 0 < b) (ordered : b ≤ a) :
    2 * (a % b) < a := by
  have remainder := Nat.mod_lt a positive
  by_cases half : 2 * b ≤ a
  · omega
  · have quotient : a % b = a - b := by
      rw [Nat.mod_eq_sub_mod ordered, Nat.mod_eq_of_lt (by omega)]
    rw [quotient]
    omega

theorem gcd_step (a b : UInt64) :
    Nat.gcd b.toNat (a % b).toNat = Nat.gcd a.toNat b.toNat := by
  rw [UInt64.toNat_mod, Nat.gcd_comm b.toNat, ← Nat.gcd_rec, Nat.gcd_comm]

theorem gcdFuel_correct (bits : ℕ) (a b : UInt64) (bound : b.toNat < 2^bits) :
    (gcdFuel (2 * bits + 1) a b).toNat = Nat.gcd a.toNat b.toNat := by
  induction bits generalizing a b with
  | zero =>
    have hb : b = 0 := by apply UInt64.toNat.inj; simp_all
    subst b
    simp [gcdFuel]
  | succ bits ih =>
    by_cases hb : b = 0
    · subst b
      simp [gcdFuel]
    · have bp : 0 < b.toNat := by
        have : b.toNat ≠ 0 := by
          intro h
          exact hb (UInt64.toNat.inj (by simpa using h))
        omega
      have fuel : 2 * (bits + 1) + 1 = (2 * bits + 1) + 2 := by omega
      rw [fuel, gcdFuel]
      simp only [beq_iff_eq, hb, ↓reduceIte]
      by_cases hr : a % b = 0
      · rw [hr, gcdFuel]
        simp only [beq_self_eq_true, ↓reduceIte]
        have step := gcd_step a b
        simpa [hr] using step
      · rw [gcdFuel]
        simp only [beq_iff_eq, hr, ↓reduceIte]
        have rp : 0 < (a % b).toNat := by
          have : (a % b).toNat ≠ 0 := by
            intro h
            exact hr (UInt64.toNat.inj (by simpa using h))
          omega
        have smaller : (a % b).toNat < b.toNat := by
          simpa using Nat.mod_lt a.toNat bp
        have twice := twice_remainder_lt b.toNat (a % b).toNat rp (by omega)
        have reduced : (b % (a % b)).toNat < 2^bits := by
          rw [UInt64.toNat_mod]
          rw [pow_succ] at bound
          omega
        rw [ih _ _ reduced, gcd_step, gcd_step]

theorem gcd129_correct (a b : UInt64) :
    (gcdFuel 129 a b).toNat = Nat.gcd a.toNat b.toNat := by
  exact gcdFuel_correct 64 a b b.toNat_lt

theorem word_positive (a : UInt64) (nonzero : a ≠ 0) : 0 < a.toNat := by
  have h : a.toNat ≠ 0 := by
    intro h
    exact nonzero (UInt64.toNat.inj (by simpa using h))
  omega

def value (a : Fraction) : ℚ :=
  (if a.negative then -1 else 1) * (a.numerator.toNat : ℚ) / (a.denominator.toNat : ℚ)

theorem fraction_exact (negative : Bool) (n d : UInt64) (denominator : d ≠ 0) :
    (fraction negative n d).denominator ≠ 0 ∧
    value (fraction negative n d) =
      (if negative then -1 else 1) * (n.toNat : ℚ) / (d.toNat : ℚ) := by
  have dp := word_positive d denominator
  have gp : 0 < (gcdFuel 129 n d).toNat := by
    rw [gcd129_correct]
    exact Nat.gcd_pos_of_pos_right _ dp
  have gn : gcdFuel 129 n d ≠ 0 := by
    intro h
    simp [h] at gp
  by_cases zeroNumerator : n = 0
  · simp [fraction, denominator, zeroNumerator, zero, value]
  · simp only [fraction, beq_iff_eq, denominator, zeroNumerator, gn, ↓reduceIte]
    constructor
    · intro h
      have hp : 0 < (d / gcdFuel 129 n d).toNat := by
        rw [UInt64.toNat_div, gcd129_correct]
        exact Nat.div_gcd_pos_of_pos_right _ dp
      simp [h] at hp
    · simp only [value, UInt64.toNat_div, gcd129_correct]
      rw [mul_div_assoc, Nat.cast_div_div_div_cancel_right
        (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _), ← mul_div_assoc]

end Project.Beck.Arithmetic
