import Project.ExpArm.OuterScale
import Project.ExpArm.PositiveAccuracy
import Project.ExpArm.NegativeNormalAccuracy

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit F64NormalScale F64Order

set_option exponentiation.threshold 4096

def negativePath (x : UInt64) : UInt64 :=
  if negativeCore x < 0x3FF0000000000000 then negativeSubnormalPath x
  else Wasm.IEEE64.mul 0x0010000000000000 (negativeCore x)

theorem positive_outer_path (x : UInt64) (hf : Finite x)
    (hx : 800 ≤ value x ∧ value x ≤ 1024) : positivePath x = 0x7FF0000000000000 := by
  have hs := positive_outer_scale x hf hx
  have ht := full_correction_bounds x hf (abs_le.mpr ⟨by linarith, hx.2⟩)
  have hr := reconstruction_bounds (positiveScale x) (pathCorrection x) hs.1 ht.1
    ((by norm_num : (2 : ℝ)^(-500 : Int) ≤ 2^140).trans hs.2.1) hs.2.2 ht.2
  change Finite (positiveCore x) ∧ value (positiveScale x)/2 ≤ value (positiveCore x) ∧
    value (positiveCore x) ≤ 2*value (positiveScale x) at hr
  have hlo : (2 : ℝ)^139 ≤ value (positiveCore x) := by
    have hp := div_le_div_of_nonneg_right hs.2.1 (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hp ⊢
    linarith [hr.2.1]
  have hn := normal_of_value (positiveCore x) hr.1
    ((by norm_num : (2 : ℝ)^(-1022 : Int) ≤ 2^139).trans hlo)
  have he : 1038 ≤ Wasm.IEEE64.exponent (positiveCore x) := by
    by_contra hh
    have hu := (positive_binade _ hn.1 hn.2).2
    have hpow : (2 : ℝ)^((Wasm.IEEE64.exponent (positiveCore x) : Int)-1022) ≤ 2^(15 : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hbad := hu.trans_le hpow
    norm_num at hbad hlo
    linarith
  have hw : positivePath x = Wasm.IEEE64.mul (positiveCore x)
      (Wasm.IEEE64.encodeFinite false 2032 0) := mul_finite_comm _ _ (by rfl) hr.1
  rw [hw, mul_power_word _ hr.1 hn.2 2032 (by decide) (by decide) (by omega),
    ite_eq_left (by omega), hn.1]
  rfl

theorem negative_outer_path (x : UInt64) (hf : Finite x)
    (hx : -1024 ≤ value x ∧ value x ≤ -800) : negativePath x = 0 := by
  have hs := negative_outer_scale x hf hx
  have ht := full_correction_bounds x hf (abs_le.mpr ⟨hx.1, by linarith⟩)
  have hu : value (negativeScale x) ≤ (2 : ℝ)^500 := hs.2.2.trans (by norm_num)
  have hp := scale_product_bound (negativeScale x) (pathCorrection x) hs.1 ht.1 hs.2.1 hu ht.2
  have hr := reconstruction_bounds (negativeScale x) (pathCorrection x) hs.1 ht.1 hs.2.1 hu ht.2
  change Finite (negativeCore x) ∧ value (negativeScale x)/2 ≤ value (negativeCore x) ∧
    value (negativeCore x) ≤ 2*value (negativeScale x) at hr
  have hsp : 0 < value (negativeScale x) :=
    (by positivity : (0 : ℝ) < 2^(-500 : Int)).trans_le hs.2.1
  have hcp : 0 < value (negativeCore x) := by linarith [hr.2.1]
  have hcu : value (negativeCore x) < 1 := by
    have hn : 2*(2 : ℝ)^(-126 : Int) < 1 := by norm_num
    linarith [hr.2.2]
  have hword : negativeCore x < 0x3FF0000000000000 :=
    (positive_word_lt_iff _ _ (positiveBits_of_finite_value_pos _ hr.1 hcp) (by decide)).mpr
      (by rwa [F64OneAdd.one_value])
  have hz := F64CompensatedSum.rounded_sum_zero (negativeScale x)
    (Wasm.IEEE64.mul (negativeScale x) (pathCorrection x)) hs.1 hp.1
    ⟨hsp, hs.2.2.trans (by norm_num)⟩ hp.2.1 hword
  rw [negativePath, ite_eq_left hword, negativeSubnormalPath, hz]
  decide

theorem negative_path_accuracy (x : UInt64) (hf : Finite x)
    (hx : -800 ≤ value x ∧ value x ≤ -512) :
    F64Accuracy.ErrorBelowOneUlp (negativePath x) (Real.exp (value x)) := by
  by_cases hy : negativeCore x < 0x3FF0000000000000
  · rw [negativePath, ite_eq_left hy]
    exact negative_subnormal_accuracy x hf hx hy
  · rw [negativePath, ite_eq_right hy]
    apply negative_normal_accuracy x hf hx
    have hn := negative_core_normal x hf hx
    have he : (negativeCore x).toNat < 2^63 := by
      simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hn.1
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hy
    dsimp [Wasm.IEEE64.exponent]
    omega

#print axioms positive_outer_path
#print axioms negative_outer_path
#print axioms negative_path_accuracy
end Project.ExpArm
