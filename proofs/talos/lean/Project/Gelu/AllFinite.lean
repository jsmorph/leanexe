import Project.Gelu.Bounds
import Project.Gelu.GlobalPerturbation

namespace Project.Gelu
open CodeLib.IEEE64

theorem evaluateAll_error (x : UInt64) (hf : Finite x) :
    Finite (evaluateAll x) ∧ |value (evaluateAll x)-Real.gelu (value x)| ≤ 1/100 := by
  unfold evaluateAll
  cases hd : inDomain x
  · simp only [Bool.false_eq_true, ite_false]
    have hx : 3 < |value x| := by
      by_contra h
      have htrue := (inDomain_iff x).mpr ⟨hf, by linarith⟩
      simp [hd] at htrue
    by_cases hs : x < 0x8000000000000000
    · rw [ite_eq_left hs]
      have hv := Softmax.value_nonnegative hs
      rw [abs_of_nonneg hv] at hx
      exact ⟨hf, by rw [abs_sub_comm]; exact Real.positive_tail _ hx.le⟩
    · rw [ite_eq_right hs]
      have hv := Softmax.value_nonpositive hs
      rw [abs_of_nonpos hv] at hx
      have hzero : value 0 = 0 := by
        norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
          Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
      refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
      rw [hzero, zero_sub, abs_neg]
      exact Real.negative_tail _ (by linarith)
  · simp only [ite_true]
    exact evaluate_error x hf ((inDomain_iff x).mp hd).2

theorem evaluateAll_perturbed (x : UInt64) (r error : ℝ) (hf : Finite x)
    (he : |value x-r| ≤ error) :
    |value (evaluateAll x)-Real.gelu r| ≤ 1/100+4*error := by
  have hn := evaluateAll_error x hf
  have hp := Real.gelu_lipschitz_global (value x) r
  exact (abs_sub_le _ _ _).trans (add_le_add hn.2 (hp.trans (by linarith)))

#print axioms evaluateAll_error
#print axioms evaluateAll_perturbed
end Project.Gelu
