import Verified.Examples.Trig
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Bounds on `π` from Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)` and the alternating
arctangent series, whose partial sums the kernel computes in rational arithmetic.  The bounds fix
the words that `Trig.remLarge` reads: `Trig.invPi` holds `2/π` truncated to 1216 bits after the
point, and `Trig.halfPi` holds `π · 2 ^ 126` truncated to an integer.
-/

namespace Verified.Examples.TrigPi

set_option exponentiation.threshold 4096

open Finset

/-- The magnitude of term `n` of the arctangent series at `x`. -/
def term (x : ℚ) (n : ℕ) : ℚ := x ^ (2 * n + 1) / (2 * n + 1)

/-- The sum of the first `n` terms of the arctangent series at `x`. -/
def partialSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => partialSum x n + (-1) ^ n * term x n

theorem partialSum_cast (x : ℚ) (n : ℕ) :
    ((partialSum x n : ℚ) : ℝ) =
      ∑ i ∈ range n, (-1 : ℝ) ^ i * ((x : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [partialSum, sum_range_succ, ← ih, term]
    push_cast
    ring

/-- The alternating series bound: the arctangent lies within the next term of each partial
sum. -/
theorem arctan_error (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |Real.arctan x - partialSum x n| ≤ term x n := by
  have hy0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hy1 : (x : ℝ) < 1 := by exact_mod_cast h1
  set f : ℕ → ℝ := fun i => (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) with hf
  have hfa : Antitone f := by
    apply antitone_nat_of_succ_le
    intro i
    simp only [hf]
    apply div_le_div₀ (by positivity) (pow_le_pow_of_le_one hy0 hy1.le (by omega))
      (by positivity)
    push_cast
    linarith
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (fun i => by simp only [hf]; positivity) (fun i => ?_)
      (summable_geometric_of_lt_one hy0 hy1)
    simp only [hf]
    rw [div_le_iff₀ (by positivity)]
    have hp : (x : ℝ) ^ (2 * i + 1) ≤ (x : ℝ) ^ i :=
      pow_le_pow_of_le_one hy0 hy1.le (by omega)
    have hpos : 0 ≤ (x : ℝ) ^ i := by positivity
    nlinarith [mul_nonneg hpos (Nat.cast_nonneg (α := ℝ) i)]
  have hb := alternating_series_error_bound f hfa hfs n
  have hs := Real.hasSum_arctan (x := (x : ℝ))
    (by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith)
  have ht : ∑' i, (-1 : ℝ) ^ i * f i = Real.arctan x := by
    rw [← hs.tsum_eq]
    congr 1
    funext i
    simp only [hf]
    push_cast
    ring
  rw [ht, ← partialSum_cast] at hb
  have hterm : f n = ((term x n : ℚ) : ℝ) := by
    simp only [hf, term]
    push_cast
    ring
  rwa [hterm] at hb

theorem pi_eq :
    Real.pi = 16 * Real.arctan ((1 / 5 : ℚ) : ℝ) - 4 * Real.arctan ((1 / 239 : ℚ) : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have h5 : ((1 / 5 : ℚ) : ℝ) = 5⁻¹ := by norm_num
  have h239 : ((1 / 239 : ℚ) : ℝ) = 239⁻¹ := by norm_num
  rw [h5, h239]
  linarith

/-- Machin's formula with 275 and 82 terms. -/
def piApprox : ℚ := 16 * partialSum (1 / 5) 275 - 4 * partialSum (1 / 239) 82

/-- The bound on the error of `piApprox`, below `2 ^ -1270`. -/
def piError : ℚ := 16 * term (1 / 5) 275 + 4 * term (1 / 239) 82

theorem pi_close : |Real.pi - piApprox| ≤ piError := by
  have h5 := arctan_error (1 / 5) (by norm_num) (by norm_num) 275
  have h239 := arctan_error (1 / 239) (by norm_num) (by norm_num) 82
  have ha : ((piApprox : ℚ) : ℝ) =
      16 * ((partialSum (1 / 5) 275 : ℚ) : ℝ) - 4 * ((partialSum (1 / 239) 82 : ℚ) : ℝ) := by
    rw [piApprox, Rat.cast_sub, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_ofNat]
  have he : ((piError : ℚ) : ℝ) =
      16 * ((term (1 / 5) 275 : ℚ) : ℝ) + 4 * ((term (1 / 239) 82 : ℚ) : ℝ) := by
    rw [piError, Rat.cast_add, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_ofNat]
  rw [ha, he, pi_eq]
  rw [abs_le] at h5 h239 ⊢
  constructor <;> linarith [h5.1, h5.2, h239.1, h239.2]

/-- The words of `Trig.invPi` as one integer, most significant word first: `2/π · 2 ^ 1216`,
truncated. -/
def tableNum : ℕ := 0xa2f9836e4e441529fc2757d1f534ddc0db6295993c439041fe5163abdebbc561b7246e3a424dd2e006492eea09d1921cfe1deb1cb129a73ee88235f52ebb4484e99c7026b45f7e413991d639835339f49c845f8bbdf9283b1ff897ffde05980fef2f118b5a0a6d1f6d367ecf27cb09b74f463f669e5fea2d7527bac7ebe5f17b3d0739f78a5292ea6bfb5fb11f8d5d0856033046fc7b6bab

/-- The words of `Trig.halfPi` as one integer: `π · 2 ^ 126`, truncated. -/
def halfNum : ℕ := 0xC90FDAA22168C234C4C6628B80DC1CD1

theorem tableNum_eq :
    tableNum = Trig.invPi.toList.foldl (fun a w => a * 2 ^ 64 + w.toNat) 0 := by
  decide +kernel

theorem halfNum_eq : halfNum = Trig.halfPi[0]!.toNat * 2 ^ 64 + Trig.halfPi[1]!.toNat := by
  decide +kernel

theorem checked :
    0 < piApprox - piError ∧
      (tableNum : ℚ) * (piApprox + piError) ≤ 2 * 2 ^ 1216 ∧
      2 * 2 ^ 1216 < ((tableNum : ℚ) + 1) * (piApprox - piError) ∧
      (halfNum : ℚ) ≤ (piApprox - piError) * 2 ^ 126 ∧
      (piApprox + piError) * 2 ^ 126 < (halfNum : ℚ) + 1 := by
  decide +kernel

theorem pi_lower : ((piApprox - piError : ℚ) : ℝ) ≤ Real.pi := by
  have h := pi_close
  rw [abs_le] at h
  push_cast
  linarith [h.1]

theorem pi_upper : Real.pi ≤ ((piApprox + piError : ℚ) : ℝ) := by
  have h := pi_close
  rw [abs_le] at h
  push_cast
  linarith [h.2]

/-- `Trig.invPi` is `2/π` truncated to 1216 bits after the point. -/
theorem table_bounds :
    (tableNum : ℝ) ≤ 2 / Real.pi * 2 ^ 1216 ∧ 2 / Real.pi * 2 ^ 1216 < (tableNum : ℝ) + 1 := by
  obtain ⟨hpos, h1, h2, -, -⟩ := checked
  have hl := pi_lower
  have hu := pi_upper
  have hpos' : (0 : ℝ) < ((piApprox - piError : ℚ) : ℝ) := by exact_mod_cast hpos
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1' : (tableNum : ℝ) * ((piApprox + piError : ℚ) : ℝ) ≤ 2 * 2 ^ 1216 := by
    exact_mod_cast h1
  have h2' : 2 * 2 ^ 1216 < ((tableNum : ℝ) + 1) * ((piApprox - piError : ℚ) : ℝ) := by
    exact_mod_cast h2
  have hN : (0 : ℝ) ≤ tableNum := Nat.cast_nonneg _
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
    nlinarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hpi]
    nlinarith

/-- `Trig.halfPi` is `π · 2 ^ 126` truncated. -/
theorem half_bounds :
    (halfNum : ℝ) ≤ Real.pi * 2 ^ 126 ∧ Real.pi * 2 ^ 126 < (halfNum : ℝ) + 1 := by
  obtain ⟨-, -, -, h3, h4⟩ := checked
  have hl := pi_lower
  have hu := pi_upper
  have h3' : (halfNum : ℝ) ≤ ((piApprox - piError : ℚ) : ℝ) * 2 ^ 126 := by exact_mod_cast h3
  have h4' : ((piApprox + piError : ℚ) : ℝ) * 2 ^ 126 < (halfNum : ℝ) + 1 := by
    exact_mod_cast h4
  constructor <;> nlinarith

#print axioms arctan_error
#print axioms pi_close
#print axioms tableNum_eq
#print axioms halfNum_eq
#print axioms checked
#print axioms table_bounds
#print axioms half_bounds

end Verified.Examples.TrigPi
