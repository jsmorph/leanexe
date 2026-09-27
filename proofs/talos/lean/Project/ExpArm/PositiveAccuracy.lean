import Project.ExpArm.AdjustedPath
import Project.ProofKit.F64Accuracy

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Accuracy Project.ProofKit.F64NormalScale

set_option exponentiation.threshold 4096

def positivePath (x : UInt64) : UInt64 := Wasm.IEEE64.mul 0x7F00000000000000 (positiveCore x)

theorem positive_path_finite_accuracy (x : UInt64) (hf : Finite x)
    (hx : 512 ≤ value x ∧ value x ≤ 800)
    (he : Wasm.IEEE64.exponent (positiveCore x) < 1038) :
    ErrorBelowOneUlp (positivePath x) (Real.exp (value x)) := by
  have h := positive_core_error x hf hx
  have hn := positive_core_normal x hf hx
  have hm := positive_reduction_bounds x hf hx
  have hp := mul_power_value (positiveCore x) h.1 hn.1 hn.2 2032
    (by decide) (by decide) (by omega) (by omega)
  have hw : positivePath x = Wasm.IEEE64.mul (positiveCore x)
      (Wasm.IEEE64.encodeFinite false 2032 0) := by
    exact mul_finite_comm _ _ (by rfl) h.1
  rw [hw]
  have hid : Real.exp (value x-1009*Real.log 2)*(2 : ℝ)^(1009 : Int) =
      Real.exp (value x) := by
    rw [Real.exp_sub, show 1009*Real.log 2 = (1009 : Nat)*Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [← hid]
  dsimp only at h
  rw [scaleFactor_zpow _ (by omega)] at h
  exact of_scaled_adjacent_binades _ _ _ _ 1009 hp.1 hp.2 h.2.1 h.2.2.1 h.2.2.2

theorem positive_path_overflow (x : UInt64) (hf : Finite x)
    (hx : 512 ≤ value x ∧ value x ≤ 800)
    (he : 1038 ≤ Wasm.IEEE64.exponent (positiveCore x)) :
    positivePath x = 0x7FF0000000000000 := by
  have h := positive_core_error x hf hx
  have hn := positive_core_normal x hf hx
  have hw : positivePath x = Wasm.IEEE64.mul (positiveCore x)
      (Wasm.IEEE64.encodeFinite false 2032 0) := by
    exact mul_finite_comm _ _ (by rfl) h.1
  rw [hw, mul_power_word _ h.1 hn.2 2032 (by decide) (by decide) (by omega),
    ite_eq_left (by omega), hn.1]
  rfl

theorem positive_overflow_bound (x : UInt64) (hf : Finite x)
    (hx : 512 ≤ value x ∧ value x ≤ 800)
    (he : 1038 ≤ Wasm.IEEE64.exponent (positiveCore x)) :
    (2 : ℝ)^1024-(2 : ℝ)^971 < Real.exp (value x) := by
  have h := positive_core_error x hf hx
  have hn := positive_core_normal x hf hx
  have hm := positive_reduction_bounds x hf hx
  have hw : (2 : ℝ)^(15 : Int) ≤ value (positiveCore x) := by
    apply le_trans _ (positive_binade _ hn.1 hn.2).1
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  dsimp only at h
  rw [scaleFactor_zpow _ (by omega)] at h
  have hl := lower_of_rounded_power _ _ _ 15 hw h.2.1 h.2.2.2
  have hscaled := mul_lt_mul_of_pos_right hl (by positivity : (0 : ℝ) < 2^1009)
  have hid : Real.exp (value x-1009*Real.log 2)*(2 : ℝ)^1009 = Real.exp (value x) := by
    rw [Real.exp_sub, show 1009*Real.log 2 = (1009 : Nat)*Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    field_simp
  rw [hid] at hscaled
  convert hscaled using 1 <;> first | rfl | norm_num

theorem positive_path_accuracy (x : UInt64) (hf : Finite x)
    (hx : 512 ≤ value x ∧ value x ≤ 800) :
    ErrorBelowOneUlp (positivePath x) (Real.exp (value x)) ∨
    positivePath x = 0x7FF0000000000000 ∧
      (2 : ℝ)^1024-(2 : ℝ)^971 < Real.exp (value x) := by
  by_cases he : Wasm.IEEE64.exponent (positiveCore x) < 1038
  · exact Or.inl (positive_path_finite_accuracy x hf hx he)
  · exact Or.inr ⟨positive_path_overflow x hf hx (by omega), positive_overflow_bound x hf hx (by omega)⟩

#print axioms positive_path_accuracy
#print axioms positive_path_finite_accuracy
#print axioms positive_path_overflow
end Project.ExpArm
