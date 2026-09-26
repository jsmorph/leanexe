import LeanExe.Examples.Beck
import Mathlib.Tactic

namespace Project.Beck.Arithmetic

open LeanExe.Examples.Beck

def value (x : UInt64) : ℤ := x.toBitVec.toInt

def Fits (x : ℤ) : Prop := -9223372036854775808 ≤ x ∧ x < 9223372036854775808

theorem bmod_exact (x : ℤ) (h : Fits x) : x.bmod (2 ^ 64) = x := by
  exact Int.bmod_eq_of_le (by norm_num; exact h.1) (by norm_num; exact h.2)

theorem add_exact (a b : UInt64) (h : Fits (value a + value b)) :
    value (a + b) = value a + value b := by
  simpa only [value, UInt64.toBitVec_add, BitVec.toInt_add] using bmod_exact _ h

theorem sub_exact (a b : UInt64) (h : Fits (value a - value b)) :
    value (a - b) = value a - value b := by
  simpa only [value, UInt64.toBitVec_sub, BitVec.toInt_sub] using bmod_exact _ h

theorem mul_exact (a b : UInt64) (h : Fits (value a * value b)) :
    value (a * b) = value a * value b := by
  simpa only [value, UInt64.toBitVec_mul, BitVec.toInt_mul] using bmod_exact _ h

theorem value_eq (x : UInt64) : value x =
    if x.toNat < 9223372036854775808 then (x.toNat : ℤ) else x.toNat - 18446744073709551616 := by
  simp only [value, BitVec.toInt_eq_toNat_cond]
  change (if 2 * x.toNat < 2 ^ 64 then (x.toNat : ℤ) else x.toNat - 2 ^ 64) = _
  split_ifs <;> omega

theorem value_nonnegative (x : UInt64) (h : 0 ≤ value x) : value x = (x.toNat : ℤ) := by
  have bound := x.toNat_lt
  rw [value_eq] at *
  split_ifs at * <;> omega

theorem value_small (x : UInt64) (h : x.toNat < 9223372036854775808) :
    value x = (x.toNat : ℤ) := by rw [value_eq, ite_eq_left h]

theorem negative_iff (x : UInt64) : negative x = true ↔ value x < 0 := by
  have bound := x.toNat_lt
  rw [value_eq]
  simp only [negative, decide_eq_true_eq, UInt64.le_iff_toNat_le]
  change 9223372036854775808 ≤ x.toNat ↔ _
  split_ifs <;> omega

theorem magnitude_exact (x : UInt64) : ((magnitude x).toNat : ℤ) = |value x| := by
  have bound := x.toNat_lt
  unfold magnitude
  by_cases hn : negative x = true
  · rw [ite_eq_left hn, UInt64.toNat_sub]
    have hx := (negative_iff x).mp hn
    rw [abs_of_neg hx, value_eq] at *
    norm_num at *
    split_ifs at * <;> omega
  · rw [ite_eq_right hn, value_eq]
    have hx : ¬value x < 0 := by simpa [negative_iff] using hn
    rw [value_eq] at hx
    split_ifs at * <;> simp_all

theorem magnitude_zero (x : UInt64) : magnitude x = 0 ↔ x = 0 := by
  have h := magnitude_exact x
  constructor
  · intro zero
    have v : value x = 0 := abs_eq_zero.mp (by simpa [zero] using h.symm)
    rw [value_eq] at v
    have bound := x.toNat_lt
    have : x.toNat = 0 := by split_ifs at v <;> omega
    exact UInt64.toNat_inj.mp this
  · intro zero
    simp [zero, magnitude, negative]

theorem denominator_growth (round : ℕ) (D speed : ℤ)
    (hD : 0 < D ∧ D ≤ 120 ^ round) (hs : 0 < speed ∧ speed ≤ 120) :
    0 < D * speed ∧ D * speed ≤ 120 ^ (round + 1) := by
  constructor
  · exact mul_pos hD.1 hs.1
  · calc
      D * speed ≤ 120 ^ round * 120 :=
        mul_le_mul hD.2 hs.2 (le_of_lt hs.1) (by positivity)
      _ = 120 ^ (round + 1) := by rw [pow_succ]

theorem update_bounds (D p d speed distance : ℤ)
    (hD : 0 < D ∧ D ≤ 120 ^ 5)
    (hp : |p| ≤ D) (hd : |d| ≤ 120)
    (hs : 0 < speed ∧ speed ≤ 120) (hg : 0 ≤ distance ∧ distance ≤ 2 * D) :
    Fits (D * speed) ∧ Fits (p * speed) ∧ Fits (distance * d) ∧
      Fits (p * speed + distance * d) ∧ Fits (distance * speed) := by
  have ps : |p * speed| ≤ 120 * D := by
    rw [abs_mul, abs_of_pos hs.1]
    nlinarith [mul_le_mul hp hs.2 (le_of_lt hs.1) (le_of_lt hD.1)]
  have gd : |distance * d| ≤ 240 * D := by
    rw [abs_mul, abs_of_nonneg hg.1]
    nlinarith [mul_le_mul hg.2 hd (abs_nonneg d) (by linarith : 0 ≤ 2 * D)]
  have total : |p * speed + distance * d| ≤ 360 * D :=
    (abs_add_le _ _).trans (by linarith)
  have ds := mul_le_mul hD.2 hs.2 (le_of_lt hs.1) (by norm_num : (0 : ℤ) ≤ 120 ^ 5)
  have gs := mul_le_mul hg.2 hs.2 (le_of_lt hs.1) (by linarith : 0 ≤ 2 * D)
  rw [abs_le] at ps gd total
  norm_num at hD ds
  dsimp [Fits]
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem shared_denominator_update (D p d speed distance : ℚ)
    (hD : D ≠ 0) (hs : speed ≠ 0) :
    (p * speed + distance * d) / (D * speed) =
      p / D + (distance / (D * speed)) * d := by
  field_simp

end Project.Beck.Arithmetic
