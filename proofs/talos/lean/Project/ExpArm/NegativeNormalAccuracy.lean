import Project.ExpArm.AdjustedPath
import Project.ProofKit.F64Accuracy

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Accuracy Project.ProofKit.F64NormalScale

set_option exponentiation.threshold 4096

theorem negative_normal_accuracy (x : UInt64) (hf : Finite x)
    (hx : -800 ≤ value x ∧ value x ≤ -512)
    (he : 1023 ≤ Wasm.IEEE64.exponent (negativeCore x)) :
    ErrorBelowOneUlp (Wasm.IEEE64.mul 0x0010000000000000 (negativeCore x))
      (Real.exp (value x)) := by
  have h := negative_core_error x hf hx
  have hn := negative_core_normal x hf hx
  have hm := negative_reduction_bounds x hf hx
  have heu : Wasm.IEEE64.exponent (negativeCore x) < 2048 := Nat.mod_lt _ (by norm_num)
  have hp := mul_power_value (negativeCore x) h.1 hn.1 hn.2 1
    (by decide) (by decide) (by omega) (by omega)
  have hw : Wasm.IEEE64.mul 0x0010000000000000 (negativeCore x) =
      Wasm.IEEE64.mul (negativeCore x) (Wasm.IEEE64.encodeFinite false 1 0) := by
    exact mul_finite_comm _ _ (by rfl) h.1
  rw [hw]
  have hid : Real.exp (value x+1022*Real.log 2)*(2 : ℝ)^(-1022 : Int) =
      Real.exp (value x) := by
    rw [Real.exp_add, show 1022*Real.log 2 = (1022 : Nat)*Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [← hid]
  dsimp only at h
  rw [scaleFactor_zpow _ (by omega)] at h
  exact of_scaled_adjacent_binades _ _ _ _ (-1022) hp.1 hp.2 h.2.1 h.2.2.1 h.2.2.2

#print axioms negative_normal_accuracy
end Project.ExpArm
