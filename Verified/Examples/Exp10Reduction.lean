import Verified.Examples.Exp10Evaluation
import Verified.Examples.Exp2Selection
import Verified.Examples.ExpShiftedBits
import LeanExe.ProofKit.F64ExactProduct

/-!
The reduction of `Exp2.exp10Core`.  With `ratio = log 2 / (128 log 10) = log10 2 / 128`, the code
rounds `x / ratio` through the product with `128 / log10 2` and the shift `0x1.8p52`, giving an
integer `k` within `1/2 + 2 ^ -31` of `x / ratio` and the key `0x4338000000000000 + k` of `exp`.
The product of `k` with the high part of `-ratio` is exact, adding `x` to it is exact, and the
low part adds a rounding error, so the computed residual lies within `2 ^ -61` of the ideal
residual `x - k ratio`, and both are at most `1/850` in magnitude.
-/

namespace Verified.Examples.Exp10Reduction
open CodeLib.IEEE64
open LeanExe.ProofKit Exp10Constants

set_option exponentiation.threshold 4096

/-- `x · 128 / log10 2`, rounded. -/
def product (x : UInt64) : UInt64 := Wasm.IEEE64.mul invWord x

/-- The shifted sum, whose bits are the key. -/
def key (x : UInt64) : UInt64 := ExpIntegerSelection.shifted (product x)

/-- The integer `k`. -/
def integer (x : UInt64) : UInt64 := ExpIntegerSelection.selected (product x)

/-- `x - k` times the high part, exact. -/
def highResidual (x : UInt64) : UInt64 := Wasm.IEEE64.add (Wasm.IEEE64.mul hiWord (integer x)) x

/-- The computed residual. -/
def residual (x : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul loWord (integer x)) (highResidual x)

/-- `log10 2 / 128`. -/
noncomputable def ratio : ℝ := Real.log 2 / (128 * Real.log 10)

/-- The bound on the ideal residual. -/
def residualBound : ℚ :=
  (1 / 2 + 1 / 2 ^ 31) * ExpReductionBounds.upperLogTwo / (128 * lowerLogTen)

theorem checked_margins :
    residualBound + 1 / 2 ^ 61 ≤ 1 / 850 ∧ residualBound ≤ 1 / 512 ∧
    1 / 2 ^ 10 ≤ (1 / 2 - 1 / 2 ^ 31) * ExpReductionBounds.lowerLogTwo / (128 * upperLogTen) := by
  decide +kernel

theorem high_magnitude : Wasm.IEEE64.scaledMagnitude hiWord = 2585827973 * 2 ^ 1034 := by
  decide +kernel

theorem enclosures :
    (ExpReductionBounds.lowerLogTwo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ExpReductionBounds.upperLogTwo ∧
      (lowerLogTen : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ upperLogTen ∧
      (0 : ℝ) < ExpReductionBounds.lowerLogTwo ∧ (0 : ℝ) < lowerLogTen := by
  obtain ⟨h1, h2⟩ := ExpReductionBounds.log_two_enclosure
  obtain ⟨h3, h4⟩ := log_ten_enclosure
  have hb := checked_reduction
  have h5 := Exp2Approximation.cast_le hb.2.2.2.2.2.1
  have h6 := Exp2Approximation.checked_coefficients.1
  have h6' := Exp2Approximation.cast_le h6
  push_cast at h5 h6'
  have hlo2 : (0 : ℝ) < ExpReductionBounds.lowerLogTwo := by
    have := ExpReductionBounds.log_two_coarse_bounds
    have h7 := Exp2Approximation.cast_le (show (0 : ℚ) ≤ ExpReductionBounds.lowerLogTwo from h6)
    push_cast at h7
    rcases h7.lt_or_eq with h | h
    · exact h
    · exfalso
      have hq : ExpReductionBounds.lowerLogTwo = 0 := by exact_mod_cast h.symm
      have : (0 : ℚ) < ExpReductionBounds.lowerLogTwo := by
        unfold ExpReductionBounds.lowerLogTwo ExpReductionBounds.splitLogTwo
        decide +kernel
      rw [hq] at this
      exact lt_irrefl _ this
  exact ⟨h1, h2, h3, h4, hlo2, by linarith⟩

theorem ratio_bounds :
    (ExpReductionBounds.lowerLogTwo : ℝ) / (128 * upperLogTen) ≤ ratio ∧
      ratio ≤ (ExpReductionBounds.upperLogTwo : ℝ) / (128 * lowerLogTen) ∧ 0 < ratio := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := enclosures
  have hL10 : 0 < Real.log 10 := by linarith
  have hL2 : 0 < Real.log 2 := by linarith
  have hu10 : (0 : ℝ) < upperLogTen := by linarith
  refine ⟨?_, ?_, div_pos hL2 (by positivity)⟩
  · rw [ratio, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [ratio, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem split_close : |value hiWord + value loWord + ratio| ≤ 1 / 2 ^ 85 := by
  obtain ⟨hlo, hhi, -⟩ := ratio_bounds
  have hb := checked_reduction
  have a := Exp2Approximation.cast_le hb.1
  have b := Exp2Approximation.cast_le hb.2.1
  push_cast at a b
  simp only [PolyBound.ratOfWord_cast] at a b
  rw [abs_le]
  constructor <;> linarith

theorem inv_close : |value invWord - 1 / ratio| ≤ 1 / 2 ^ 40 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := enclosures
  have hb := checked_reduction
  have a := Exp2Approximation.cast_le hb.2.2.1
  have b := Exp2Approximation.cast_le hb.2.2.2.1
  push_cast at a b
  simp only [PolyBound.ratOfWord_cast] at a b
  have hL10 : 0 < Real.log 10 := by linarith
  have hL2 : 0 < Real.log 2 := by linarith
  have hinv : 1 / ratio = 128 * Real.log 10 / Real.log 2 := by
    rw [ratio, one_div_div]
  have hup : 128 * Real.log 10 / Real.log 2 ≤ 128 * (upperLogTen : ℝ) /
      ExpReductionBounds.lowerLogTwo := by
    rw [div_le_div_iff₀ hL2 h5]
    nlinarith
  have hlow : 128 * (lowerLogTen : ℝ) / ExpReductionBounds.upperLogTwo ≤
      128 * Real.log 10 / Real.log 2 := by
    rw [div_le_div_iff₀ (by linarith) hL2]
    nlinarith
  rw [hinv, abs_le]
  constructor <;> linarith

/-- A finite word of magnitude at least `2 ^ -10` has a scaled value divisible by `2 ^ 1012`. -/
theorem scaled_dvd (x : UInt64) (hx : (1 : ℝ) / 2 ^ 10 ≤ |value x|) :
    (2 : Int) ^ 1012 ∣ Wasm.IEEE64.scaledValue x := by
  have he : 1013 ≤ Wasm.IEEE64.exponent x := by
    by_contra hn
    have h := F64Magnitude.magnitude_lt x 1013 (-10) (by norm_num) (by norm_num) (by omega)
    norm_num at h
    linarith
  have hm : Wasm.IEEE64.scaledMagnitude x =
      (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ (Wasm.IEEE64.exponent x - 1 - 1012) * 2 ^ 1012 := by
    have h0 : Wasm.IEEE64.exponent x ≠ 0 := by omega
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, h0, ite_false]
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have hdN : 2 ^ 1012 ∣ Wasm.IEEE64.scaledMagnitude x := by
    rw [hm]
    exact Dvd.intro_left _ rfl
  have hd : (2 : Int) ^ 1012 ∣ (Wasm.IEEE64.scaledMagnitude x : Int) := by exact_mod_cast hdN
  unfold Wasm.IEEE64.scaledValue
  split
  · exact (Int.dvd_neg).mpr hd
  · exact hd

theorem reduction_state (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 400) :
    ∃ k : Int, Finite (integer x) ∧ value (integer x) = (k : ℝ) ∧ k.natAbs ≤ 2 ^ 18 ∧
      ((key x).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      |value x - (k : ℝ) * ratio| ≤ residualBound ∧
      |(k : ℝ) - value x / ratio| ≤ 1 / 2 + 1 / 2 ^ 31 ∧
      Finite (residual x) ∧ |value (residual x) - (value x - (k : ℝ) * ratio)| ≤ 1 / 2 ^ 61 ∧
      |value (residual x)| ≤ 1 / 850 := by
  obtain ⟨f1, f2, f3, f4, f5, fhi, flo, finv⟩ := coefficient_finite
  obtain ⟨-, -, -, -, -, bhi, blo, binv⟩ := coefficient_bounds
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hm : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  obtain ⟨hrlo, hrhi, hrpos⟩ := ratio_bounds
  obtain ⟨hmarg, hmarg2, hmarg3⟩ := checked_margins
  have hm1 := Exp2Approximation.cast_le hmarg
  have hm2 := Exp2Approximation.cast_le hmarg2
  have hm3 := Exp2Approximation.cast_le hmarg3
  push_cast at hm1 hm2 hm3
  have hr0 : ratio ≠ 0 := hrpos.ne'
  -- the product with `128 / log10 2`
  have hcx : |value invWord * value x| ≤ 170400 := by
    rw [abs_mul]
    calc
      _ ≤ 426 * 400 := mul_le_mul binv hx (abs_nonneg _) (by norm_num)
      _ = 170400 := by norm_num
  obtain ⟨hpf, hpe⟩ := F64MulBounds.mul_real_mixed invWord x finv hxf
    (hcx.trans_lt (by norm_num))
  have hpe' : |value (product x) - value invWord * value x| ≤ 1 / 2 ^ 35 := by
    refine hpe.trans ?_
    rw [hu, hm]
    calc
      _ ≤ (1 : ℝ) / 2 ^ 53 * 170400 + 1 / 2 ^ 1075 := by gcongr
      _ ≤ 1 / 2 ^ 35 := by norm_num
  have hpb : |value (product x)| ≤ (2 : ℝ) ^ 18 := by
    have := abs_sub_abs_le_abs_sub (value (product x)) (value invWord * value x)
    have : (170400 : ℝ) + 1 / 2 ^ 35 ≤ 2 ^ 18 := by norm_num
    linarith
  -- the integer `k`
  obtain ⟨k, hsf, hsv, hkn, hki⟩ := ExpShiftedBits.shifted_encoding (product x) hpf hpb
  obtain ⟨k', -, hsv', -, hke⟩ := ExpIntegerSelection.selected_integer (product x) hpf hpb
  have hkk : k' = k :=
    mul_right_cancel₀ (by positivity : (2 : Int) ^ 1074 ≠ 0) (hsv'.symm.trans hsv)
  subst hkk
  have hkv : value (integer x) = (k' : ℝ) := by
    rw [integer, value, hsv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      mul_div_cancel_right₀ _ (by positivity)]
  have hkn' : k'.natAbs ≤ 2 ^ 18 := hkn
  -- the ideal residual
  have hinv := inv_close
  have hdiff : |(k' : ℝ) - value x / ratio| ≤ 1 / 2 + 1 / 2 ^ 31 := by
    have h1 : |value x * value invWord - value x / ratio| ≤ 400 * (1 / 2 ^ 40) := by
      rw [show value x * value invWord - value x / ratio =
        value x * (value invWord - 1 / ratio) by rw [mul_sub, mul_one_div], abs_mul]
      exact mul_le_mul hx hinv (abs_nonneg _) (by norm_num)
    calc
      _ = |((k' : ℝ) - value (product x)) + (value (product x) - value invWord * value x) +
          (value x * value invWord - value x / ratio)| := by congr 1; ring
      _ ≤ |(k' : ℝ) - value (product x)| + |value (product x) - value invWord * value x| +
          |value x * value invWord - value x / ratio| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 ^ 35 + 400 * (1 / 2 ^ 40) := by gcongr
      _ ≤ 1 / 2 + 1 / 2 ^ 31 := by norm_num
  have hideal : |value x - (k' : ℝ) * ratio| ≤ residualBound := by
    have hid : value x - (k' : ℝ) * ratio = -(((k' : ℝ) - value x / ratio) * ratio) := by
      rw [sub_mul, div_mul_cancel₀ _ hr0]
      ring
    rw [hid, abs_neg, abs_mul, abs_of_pos hrpos]
    push_cast [residualBound]
    calc
      _ ≤ (1 / 2 + 1 / 2 ^ 31) * ratio := mul_le_mul_of_nonneg_right hdiff hrpos.le
      _ ≤ (1 / 2 + 1 / 2 ^ 31) * ((ExpReductionBounds.upperLogTwo : ℝ) / (128 * lowerLogTen)) :=
        mul_le_mul_of_nonneg_left hrhi (by norm_num)
      _ = _ := by ring
  -- the exact product with the high part and the exact sum with `x`
  have hik : Wasm.IEEE64.scaledMagnitude (integer x) = k'.natAbs * 2 ^ 1074 := by
    have h := natAbs_scaledValue (ExpIntegerSelection.selected (product x))
    rw [hsv, Int.natAbs_mul] at h
    show Wasm.IEEE64.scaledMagnitude (ExpIntegerSelection.selected (product x)) = _
    simpa using h.symm
  have hif : Finite (integer x) := hsf
  obtain ⟨hhf, hhv, hhm0, -⟩ := F64ExactProduct.mul_exact_scaled hiWord (integer x) fhi hif
    2585827973 k'.natAbs 1034 1074 high_magnitude hik (by
      have : k'.natAbs ≤ 2 ^ 18 := hkn'
      calc
        2585827973 * k'.natAbs ≤ 2585827973 * 2 ^ 18 := Nat.mul_le_mul_left _ this
        _ < 2 ^ 53 := by norm_num) (by norm_num) (by norm_num)
  rw [hkv] at hhv
  have hhm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul hiWord (integer x)) =
      2585827973 * k'.natAbs * 2 ^ 1034 := by
    rw [hhm0]
  have hsplit := split_close
  have hkz : |k'| ≤ (2 : ℤ) ^ 18 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hkn'
  have hk18 : |(k' : ℝ)| ≤ 2 ^ 18 := by
    have := (Int.cast_le (R := ℝ)).mpr hkz
    push_cast at this
    linarith
  have hxh : |value x + value hiWord * (k' : ℝ)| ≤ 1 / 2 ^ 9 := by
    have hi1 : |value x - (k' : ℝ) * ratio| ≤ 1 / 850 := by linarith [hideal, hm1]
    have hlowk : |value loWord * (k' : ℝ)| ≤ 1 / 2 ^ 45 * 2 ^ 18 := by
      rw [abs_mul]
      exact mul_le_mul blo hk18 (abs_nonneg _) (by positivity)
    have hsk : |(value hiWord + value loWord + ratio) * (k' : ℝ)| ≤ 1 / 2 ^ 85 * 2 ^ 18 := by
      rw [abs_mul]
      exact mul_le_mul hsplit hk18 (abs_nonneg _) (by positivity)
    have hid : value x + value hiWord * (k' : ℝ) = (value x - (k' : ℝ) * ratio) +
        (value hiWord + value loWord + ratio) * (k' : ℝ) - value loWord * (k' : ℝ) := by ring
    rw [hid]
    calc
      _ ≤ |value x - (k' : ℝ) * ratio| + |(value hiWord + value loWord + ratio) * (k' : ℝ)| +
          |value loWord * (k' : ℝ)| := by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
      _ ≤ 1 / 850 + 1 / 2 ^ 85 * 2 ^ 18 + 1 / 2 ^ 45 * 2 ^ 18 := by gcongr
      _ ≤ 1 / 2 ^ 9 := by norm_num
  have hhr : Finite (highResidual x) ∧
      value (highResidual x) = value x + value hiWord * (k' : ℝ) := by
    by_cases hk0 : k' = 0
    · subst hk0
      have hz : Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul hiWord (integer x)) = 0 := by
        unfold Wasm.IEEE64.scaledValue
        rw [hhm]
        simp
      have hx400 : Wasm.IEEE64.exponent x ≤ 1031 := by
        by_contra hn
        have h := F64Magnitude.magnitude_ge x 1032 9 (by norm_num) (by norm_num) (by norm_num)
          (by omega)
        norm_num at h
        linarith
      obtain ⟨hd, hbd⟩ := Exp2Selection.word_grid x
      have h := F64ErrorTrack.add_exact_grid _ x hhf hxf (Wasm.IEEE64.exponent x - 1) (by omega)
        (by rw [hz]; exact dvd_zero _) hd (by rw [hz, zero_add]; exact hbd)
      refine ⟨h.1, ?_⟩
      rw [highResidual, h.2, hhv]
      push_cast
      ring
    · have hk1 : (1 : ℝ) ≤ |(k' : ℝ)| := by
        have : (1 : Int) ≤ |k'| := Int.one_le_abs hk0
        exact_mod_cast this
      have hx10 : (1 : ℝ) / 2 ^ 10 ≤ |value x| := by
        have h1 : 1 / 2 - 1 / 2 ^ 31 ≤ |value x / ratio| := by
          have := abs_sub_abs_le_abs_sub (k' : ℝ) (value x / ratio)
          linarith
        rw [abs_div, abs_of_pos hrpos, le_div_iff₀ hrpos] at h1
        calc
          (1 : ℝ) / 2 ^ 10 ≤ (1 / 2 - 1 / 2 ^ 31) * ((ExpReductionBounds.lowerLogTwo : ℝ) /
              (128 * upperLogTen)) := by rw [← mul_div_assoc]; exact hm3
          _ ≤ (1 / 2 - 1 / 2 ^ 31) * ratio := mul_le_mul_of_nonneg_left hrlo (by norm_num)
          _ ≤ _ := h1
      have hdh : (2 : Int) ^ 1012 ∣ Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul hiWord (integer x)) := by
        have hdN : 2 ^ 1012 ∣ Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul hiWord (integer x)) := by
          rw [hhm]
          exact Dvd.intro (2585827973 * k'.natAbs * 2 ^ 22) (by ring)
        have hd : (2 : Int) ^ 1012 ∣
            (Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul hiWord (integer x)) : Int) := by
          exact_mod_cast hdN
        unfold Wasm.IEEE64.scaledValue
        split
        · exact (Int.dvd_neg).mpr hd
        · exact hd
      have hbound : |Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul hiWord (integer x)) +
          Wasm.IEEE64.scaledValue x| ≤ 2 ^ 53 * 2 ^ 1012 := by
        have hR : |((Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul hiWord (integer x)) +
            Wasm.IEEE64.scaledValue x : Int) : ℝ)| ≤ (2 : ℝ) ^ 53 * 2 ^ 1012 := by
          have hsum := F64Magnitude.sum_scaled (Wasm.IEEE64.mul hiWord (integer x)) x
          rw [hhv] at hsum
          have hval : ((Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul hiWord (integer x)) +
              Wasm.IEEE64.scaledValue x : Int) : ℝ) =
              (value hiWord * (k' : ℝ) + value x) * 2 ^ 1074 := by
            rw [hsum]
            field_simp
          rw [hval, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), add_comm]
          calc
            _ ≤ 1 / 2 ^ 9 * (2 : ℝ) ^ 1074 := mul_le_mul_of_nonneg_right hxh (by positivity)
            _ = _ := by norm_num
        exact_mod_cast hR
      have h := F64ErrorTrack.add_exact_grid _ x hhf hxf 1012 (by norm_num) hdh (scaled_dvd x hx10)
        hbound
      refine ⟨h.1, ?_⟩
      rw [highResidual, h.2, hhv]
      ring
  -- the low part and the final rounding
  have hlk : |value loWord * (k' : ℝ)| ≤ 1 / 2 ^ 27 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 45 * 2 ^ 18 := mul_le_mul blo hk18 (abs_nonneg _) (by positivity)
      _ = 1 / 2 ^ 27 := by norm_num
  have hlk' : |value loWord * value (integer x)| < (2 : ℝ) ^ 1022 := by
    rw [hkv]
    exact hlk.trans_lt (by norm_num)
  obtain ⟨hlf, hle⟩ := F64MulBounds.mul_real_mixed loWord (integer x) flo hif hlk'
  rw [hkv] at hle
  have hle' : |value (Wasm.IEEE64.mul loWord (integer x)) - value loWord * (k' : ℝ)| ≤
      1 / 2 ^ 79 := by
    refine hle.trans ?_
    rw [hu, hm]
    calc
      _ ≤ (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 27) + 1 / 2 ^ 1075 := by gcongr
      _ ≤ 1 / 2 ^ 79 := by norm_num
  have hsk : |(value hiWord + value loWord + ratio) * (k' : ℝ)| ≤ 1 / 2 ^ 85 * 2 ^ 18 := by
    rw [abs_mul]
    exact mul_le_mul hsplit hk18 (abs_nonneg _) (by positivity)
  have hsum : |value (Wasm.IEEE64.mul loWord (integer x)) + value (highResidual x)| ≤ 1 / 2 ^ 9 := by
    have hid : value (Wasm.IEEE64.mul loWord (integer x)) + value (highResidual x) =
        (value (Wasm.IEEE64.mul loWord (integer x)) - value loWord * (k' : ℝ)) +
          (value x - (k' : ℝ) * ratio) + (value hiWord + value loWord + ratio) * (k' : ℝ) := by
      rw [hhr.2]
      ring
    have hi1 : |value x - (k' : ℝ) * ratio| ≤ 1 / 850 := by linarith [hideal, hm1]
    rw [hid]
    calc
      _ ≤ |value (Wasm.IEEE64.mul loWord (integer x)) - value loWord * (k' : ℝ)| +
          |value x - (k' : ℝ) * ratio| + |(value hiWord + value loWord + ratio) * (k' : ℝ)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
      _ ≤ 1 / 2 ^ 79 + 1 / 850 + 1 / 2 ^ 85 * 2 ^ 18 := by gcongr
      _ ≤ 1 / 2 ^ 9 := by norm_num
  obtain ⟨hrf, hre⟩ := F64AddBounds.add_real_relative _ _ hlf hhr.1
    (hsum.trans_lt (by norm_num))
  have hre' : |value (residual x) -
      (value (Wasm.IEEE64.mul loWord (integer x)) + value (highResidual x))| ≤ 1 / 2 ^ 61 / 2 := by
    refine hre.trans ?_
    rw [hu]
    calc
      _ ≤ (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 9) := by gcongr
      _ ≤ 1 / 2 ^ 61 / 2 := by norm_num
  have herr : |value (residual x) - (value x - (k' : ℝ) * ratio)| ≤ 1 / 2 ^ 61 := by
    have hid : value (residual x) - (value x - (k' : ℝ) * ratio) =
        (value (residual x) - (value (Wasm.IEEE64.mul loWord (integer x)) +
          value (highResidual x))) +
        (value (Wasm.IEEE64.mul loWord (integer x)) - value loWord * (k' : ℝ)) +
        (value hiWord + value loWord + ratio) * (k' : ℝ) := by
      rw [hhr.2]
      ring
    rw [hid]
    calc
      _ ≤ |value (residual x) - (value (Wasm.IEEE64.mul loWord (integer x)) +
            value (highResidual x))| +
          |value (Wasm.IEEE64.mul loWord (integer x)) - value loWord * (k' : ℝ)| +
          |(value hiWord + value loWord + ratio) * (k' : ℝ)| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
      _ ≤ 1 / 2 ^ 61 / 2 + 1 / 2 ^ 79 + 1 / 2 ^ 85 * 2 ^ 18 := by gcongr
      _ ≤ 1 / 2 ^ 61 := by norm_num
  refine ⟨k', hif, hkv, hkn', hki, hideal, hdiff, hrf, herr, ?_⟩
  have := abs_sub_abs_le_abs_sub (value (residual x)) (value x - (k' : ℝ) * ratio)
  linarith

#print axioms checked_margins
#print axioms high_magnitude
#print axioms ratio_bounds
#print axioms split_close
#print axioms inv_close
#print axioms scaled_dvd
#print axioms reduction_state

end Verified.Examples.Exp10Reduction
