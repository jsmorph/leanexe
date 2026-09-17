import Project.GeluWide.Numerical
import Project.GeluWide.Tail
import Project.Gelu.GlobalPerturbation
import Project.ProofKit.F64Bounded

namespace Project.GeluWide
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem eight_value : value 0x4020000000000000 = 8 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem inCore_iff (x : UInt64) : inCore x = true ↔ Finite x ∧ |value x| ≤ 8 := by
  have hh := F64Order.absBits_le_iff x 0x4020000000000000
    (by unfold CodeLib.IEEE64.Finite; decide)
  simpa only [inCore, decide_eq_true_eq,
    show F64Order.absBits 0x4020000000000000 = 0x4020000000000000 by decide,
    eight_value, abs_of_pos (by norm_num : (0:ℝ)<8)] using hh

theorem evaluateAll_error (x : UInt64) (hf : Finite x) :
    Finite (evaluateAll x) ∧ |value (evaluateAll x)-Gelu.Real.gelu (value x)| ≤
      200000*arithmeticEpsilon := by
  unfold evaluateAll
  cases hd : inCore x
  · simp only [Bool.false_eq_true, ite_false]
    have hx : 8 < |value x| := by
      by_contra hh
      have htrue := (inCore_iff x).mpr ⟨hf, by linarith⟩
      simp [hd] at htrue
    have heps : (1:ℝ)/10^18 ≤ 200000*arithmeticEpsilon := by norm_num [arithmeticEpsilon]
    by_cases hs : x < 0x8000000000000000
    · rw [ite_eq_left hs]
      have hv := Softmax.value_nonnegative hs
      rw [abs_of_nonneg hv] at hx
      exact ⟨hf, by rw [abs_sub_comm]; exact (positive_tail _ hx.le).trans heps⟩
    · rw [ite_eq_right hs]
      have hv := Softmax.value_nonpositive hs
      rw [abs_of_nonpos hv] at hx
      refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
      rw [ExpSmall.zero_value, zero_sub, abs_neg]
      exact (negative_tail _ (by linarith)).trans heps
  · simp only [ite_true]
    exact evaluate_error x hf ((inCore_iff x).mp hd).2

theorem evaluateAll_perturbed (x : UInt64) (r error : ℝ) (hf : Finite x)
    (he : |value x-r| ≤ error) :
    |value (evaluateAll x)-Gelu.Real.gelu r| ≤ 200000*arithmeticEpsilon+4*error := by
  have hn := evaluateAll_error x hf
  have hp := Gelu.Real.gelu_lipschitz_global (value x) r
  exact (abs_sub_le _ _ _).trans (add_le_add hn.2 (hp.trans (by linarith)))

def NumericalResult (x : UInt64) (r : ExpSmall.Result) : Prop :=
  r.status = 0 ∧ Finite r.bits ∧
    |value r.bits-Gelu.Real.gelu (value x)| ≤ 200000*arithmeticEpsilon

theorem geluWide_numerical (x : UInt64) (hf : Finite x) : NumericalResult x (geluWide x) := by
  have hd := (F64Order.finiteBits_iff x).mpr hf
  have he := evaluateAll_error x hf
  simpa only [NumericalResult, geluWide, hd, Bool.true_eq, ite_true, true_and] using he

#print axioms evaluateAll_error
#print axioms evaluateAll_perturbed
#print axioms geluWide_numerical
end Project.GeluWide
