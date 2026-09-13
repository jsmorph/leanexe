import Project.ProofKit.F64Admissibility

namespace Project.ProofKit.F64NormalizeTiny
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Normalize
open Project.ProofKit.F64Admissibility (normalizable normalizable_spec finite_exponent_bound)

noncomputable def exactMagnitude (bits top : UInt64) : ℝ :=
  |value bits| * (2 : ℝ)^1021 / (2 : ℝ)^top.toNat

def tiny (bits top : UInt64) : Bool := decide (exponentBits bits + 1021 ≤ top)

def momentumNormalizable (bits top : UInt64) : Bool :=
  normalizable bits top || tiny bits top

def normalizedMomentum (bits top : UInt64) : UInt64 :=
  if normalizable bits top then normalizedMagnitude bits top else 0

theorem scaledMagnitude_bound (bits : UInt64) :
    Wasm.IEEE64.scaledMagnitude bits < 2^(52 + Wasm.IEEE64.exponent bits) := by
  have hf : Wasm.IEEE64.fraction bits < 2^52 := Nat.mod_lt _ (by positivity)
  simp only [Wasm.IEEE64.scaledMagnitude]
  by_cases he : Wasm.IEEE64.exponent bits = 0
  · simpa only [he, beq_self_eq_true, ite_true, Nat.add_zero] using hf
  · simp only [beq_iff_eq, he, ite_false]
    calc
      (2^52 + Wasm.IEEE64.fraction bits) * 2^(Wasm.IEEE64.exponent bits - 1) <
          2^53 * 2^(Wasm.IEEE64.exponent bits - 1) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num at hf ⊢; omega) (by positivity)
      _ = 2^(52 + Wasm.IEEE64.exponent bits) := by
        rw [← pow_add]
        congr 1
        omega

set_option exponentiation.threshold 4096 in
theorem exactMagnitude_eq (bits top : UInt64) :
    exactMagnitude bits top =
      (Wasm.IEEE64.scaledMagnitude bits : ℝ) / (2 : ℝ)^(top.toNat + 53) := by
  rw [exactMagnitude, abs_value_scaledMagnitude, pow_add]
  field_simp

theorem exactMagnitude_nonneg (bits top : UInt64) : 0 ≤ exactMagnitude bits top := by
  unfold exactMagnitude
  positivity

theorem exactMagnitude_lt_of_gap (bits top : UInt64) (gap : Nat)
    (hGap : Wasm.IEEE64.exponent bits + gap ≤ top.toNat) :
    exactMagnitude bits top < 1 / (2 : ℝ)^(gap + 1) := by
  rw [exactMagnitude_eq]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have hMag : (Wasm.IEEE64.scaledMagnitude bits : ℝ) <
      (2 : ℝ)^(52 + Wasm.IEEE64.exponent bits) := by
    exact_mod_cast scaledMagnitude_bound bits
  calc
    (Wasm.IEEE64.scaledMagnitude bits : ℝ) * (2 : ℝ)^(gap + 1) <
        (2 : ℝ)^(52 + Wasm.IEEE64.exponent bits) * 2^(gap + 1) :=
      mul_lt_mul_of_pos_right hMag (by positivity)
    _ = (2 : ℝ)^(52 + Wasm.IEEE64.exponent bits + (gap + 1)) := (pow_add _ _ _).symm
    _ ≤ (2 : ℝ)^(top.toNat + 53) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = 1 * (2 : ℝ)^(top.toNat + 53) := by ring

theorem tiny_spec (bits top : UInt64) (hf : Finite bits) (ht : tiny bits top = true) :
    Wasm.IEEE64.exponent bits + 1021 ≤ top.toNat := by
  have he := finite_exponent_bound bits hf
  have hAdd : (exponentBits bits + 1021).toNat = Wasm.IEEE64.exponent bits + 1021 := by
    rw [UInt64.toNat_add, exponentBits_toNat]
    change (Wasm.IEEE64.exponent bits + 1021) % 2^64 = _
    omega
  simpa only [tiny, decide_eq_true_eq, UInt64.le_iff_toNat_le, hAdd] using ht

set_option exponentiation.threshold 4096 in
theorem tiny_magnitude_bound (bits top : UInt64) (hf : Finite bits)
    (ht : tiny bits top = true) : exactMagnitude bits top < arithmeticEpsilon := by
  have h := exactMagnitude_lt_of_gap bits top 1021 (tiny_spec bits top hf ht)
  exact h.trans_le (by norm_num [arithmeticEpsilon])

theorem normalizedMagnitude_exact (bits top : UInt64)
    (hf : Finite bits) (ht : top.toNat ≤ 2046)
    (hle : Wasm.IEEE64.exponent bits ≤ top.toNat)
    (hn : normalizable bits top = true) :
    value (normalizedMagnitude bits top) = exactMagnitude bits top := by
  have h := normalizedMagnitude_spec bits top ht hle (normalizable_spec bits top hf hn)
  exact (eq_div_iff (by positivity : (2 : ℝ)^top.toNat ≠ 0)).mpr h.2.2

theorem normalizedMomentum_spec (bits top : UInt64)
    (hf : Finite bits) (ht : top.toNat ≤ 2046)
    (hle : Wasm.IEEE64.exponent bits ≤ top.toNat)
    (hn : momentumNormalizable bits top = true) :
    Finite (normalizedMomentum bits top) ∧
      |value (normalizedMomentum bits top)| ≤ 1 / 2 ∧
      0 ≤ value (normalizedMomentum bits top) ∧
      value (normalizedMomentum bits top) ≤ exactMagnitude bits top ∧
      0 ≤ (exactMagnitude bits top)^2 - (value (normalizedMomentum bits top))^2 ∧
      (exactMagnitude bits top)^2 - (value (normalizedMomentum bits top))^2 ≤
        arithmeticEpsilon^2 := by
  by_cases hOld : normalizable bits top = true
  · rw [normalizedMomentum, ite_eq_left hOld]
    have h := normalizedMagnitude_spec bits top ht hle (normalizable_spec bits top hf hOld)
    have hExact := normalizedMagnitude_exact bits top hf ht hle hOld
    refine ⟨h.1, h.2.1, ?_⟩
    rw [hExact]
    exact ⟨exactMagnitude_nonneg bits top, le_rfl, by simp,
      by simpa only [sub_self] using sq_nonneg arithmeticEpsilon⟩
  · have hTiny : tiny bits top = true := by
      exact (Bool.or_eq_true_iff.mp hn).resolve_left hOld
    have hBound := tiny_magnitude_bound bits top hf hTiny
    have hNonneg := exactMagnitude_nonneg bits top
    have hZero : value (0 : UInt64) = 0 := by
      norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
        Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
    rw [normalizedMomentum, ite_eq_right hOld, hZero]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num, le_rfl, hNonneg, ?_, ?_⟩
    · simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
      exact sq_nonneg _
    · simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
      exact (sq_le_sq₀ hNonneg (by norm_num [arithmeticEpsilon])).mpr hBound.le

#print axioms exactMagnitude_lt_of_gap
#print axioms tiny_magnitude_bound
#print axioms normalizedMomentum_spec
end Project.ProofKit.F64NormalizeTiny
