import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64NearestBinade
import LeanExe.ProofKit.F64ExponentBounds

/-!
Sterbenz's lemma for binary64 words: a difference no larger than either operand in magnitude is
exact.  Both scaled values are multiples of `2 ^ (e - 1)` for the smaller exponent field `e`, and
the difference is at most the smaller magnitude, which fits in 53 bits on that grid, so
`F64ErrorTrack.sub_exact_grid` applies.
-/

namespace LeanExe.ProofKit.F64Sterbenz
open CodeLib.IEEE64

theorem magnitude_dvd (w : UInt64) :
    2 ^ (Wasm.IEEE64.exponent w - 1) ∣ Wasm.IEEE64.scaledMagnitude w := by
  unfold Wasm.IEEE64.scaledMagnitude
  by_cases h : Wasm.IEEE64.exponent w = 0
  · simp only [h, beq_self_eq_true, ↓reduceIte, Nat.zero_sub, pow_zero]
    exact one_dvd _
  · have h' : (Wasm.IEEE64.exponent w == 0) = false := by simpa using h
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    exact Dvd.intro_left _ rfl

theorem magnitude_lt (w : UInt64) :
    Wasm.IEEE64.scaledMagnitude w < 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  unfold Wasm.IEEE64.scaledMagnitude
  by_cases h : Wasm.IEEE64.exponent w = 0
  · simp only [h, beq_self_eq_true, ↓reduceIte, Nat.zero_sub, pow_zero, mul_one]
    omega
  · have h' : (Wasm.IEEE64.exponent w == 0) = false := by simpa using h
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

theorem value_abs_scaled (w : UInt64) :
    |value w| * 2 ^ 1074 = (Wasm.IEEE64.scaledMagnitude w : ℝ) := by
  rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
    div_mul_cancel₀ _ (by positivity)]
  rw [← Int.cast_abs, ← Int.natCast_natAbs, natAbs_scaledValue, Int.cast_natCast]

theorem scaled_dvd (w : UInt64) (s : Nat) (hs : s ≤ Wasm.IEEE64.exponent w - 1) :
    (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue w := by
  have h1 : 2 ^ s ∣ Wasm.IEEE64.scaledMagnitude w :=
    (Nat.pow_dvd_pow 2 hs).trans (magnitude_dvd w)
  have h2 : ((2 ^ s : Nat) : Int) ∣ ((Wasm.IEEE64.scaledMagnitude w : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr h1
  push_cast at h2
  unfold Wasm.IEEE64.scaledValue
  split
  · exact (dvd_neg).mpr h2
  · exact h2

/-- Sterbenz's lemma: a difference at most each operand in magnitude is exact, for `b` below
`2 ^ 1021` in magnitude. -/
theorem sub_exact (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hab : |value a - value b| ≤ |value a|) (hba : |value a - value b| ≤ |value b|)
    (hbig : |value b| < 2 ^ 1021) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  have hea : Wasm.IEEE64.exponent a < 2048 := Nat.mod_lt _ (by norm_num)
  have heb : Wasm.IEEE64.exponent b < 2044 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt b 2044 (by norm_num)
    show |value b| < |value (UInt64.ofNat (2044 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 2044 1021 (by norm_num) (by norm_num) (by norm_num),
      abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ (1021 : Int))]
    exact lt_of_lt_of_le hbig (le_of_eq (by norm_num))
  set s := min (Wasm.IEEE64.exponent a) (Wasm.IEEE64.exponent b) - 1 with hs
  have hdiff : |((Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b : Int) : ℝ)| =
      |value a - value b| * 2 ^ 1074 := by
    rw [show value a - value b = ((Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b : Int) : ℝ) /
      2 ^ 1074 by simp only [value]; push_cast; ring, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), div_mul_cancel₀ _ (by positivity)]
  have hbound : |Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b| ≤ 2 ^ 53 * 2 ^ s := by
    have h : |((Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b : Int) : ℝ)| ≤
        (((2 ^ 53 * 2 ^ s : Nat) : Int) : ℝ) := by
      rw [hdiff]
      rcases le_total (Wasm.IEEE64.exponent a) (Wasm.IEEE64.exponent b) with h | h
      · have hs' : s = Wasm.IEEE64.exponent a - 1 := by rw [hs, min_eq_left h]
        have hlt := magnitude_lt a
        have hlt' : (Wasm.IEEE64.scaledMagnitude a : ℝ) ≤ ((2 ^ 53 * 2 ^ s : Nat) : ℝ) := by
          rw [hs']
          exact_mod_cast hlt.le
        have := mul_le_mul_of_nonneg_right hab (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
        rw [value_abs_scaled] at this
        push_cast at hlt' ⊢
        linarith
      · have hs' : s = Wasm.IEEE64.exponent b - 1 := by rw [hs, min_eq_right h]
        have hlt := magnitude_lt b
        have hlt' : (Wasm.IEEE64.scaledMagnitude b : ℝ) ≤ ((2 ^ 53 * 2 ^ s : Nat) : ℝ) := by
          rw [hs']
          exact_mod_cast hlt.le
        have := mul_le_mul_of_nonneg_right hba (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
        rw [value_abs_scaled] at this
        push_cast at hlt' ⊢
        linarith
    have h2 : (|Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b| : Int) ≤
        ((2 ^ 53 * 2 ^ s : Nat) : Int) := by
      have : ((|Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b| : Int) : ℝ) ≤
          (((2 ^ 53 * 2 ^ s : Nat) : Int) : ℝ) := by
        rw [Int.cast_abs]
        exact h
      exact_mod_cast this
    push_cast at h2
    exact h2
  exact F64ErrorTrack.sub_exact_grid a b ha hb s (by omega)
    (scaled_dvd a s (by omega)) (scaled_dvd b s (by omega)) hbound

#print axioms magnitude_dvd
#print axioms magnitude_lt
#print axioms scaled_dvd
#print axioms sub_exact

end LeanExe.ProofKit.F64Sterbenz
