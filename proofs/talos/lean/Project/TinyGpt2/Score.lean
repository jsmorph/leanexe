import Project.TinyGpt2.Model
import Project.Affine.Numerical
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem sqrtTwo_bounds : 1 ≤ value 0x3FF6A09E667F3BCD ∧
    Approximation 0x3FF6A09E667F3BCD (Real.sqrt 2) 2 (1/1000000000000000) := by
  have hv : value 0x3FF6A09E667F3BCD = 6369051672525773/4503599627370496 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  refine ⟨by rw [hv]; norm_num, by unfold CodeLib.IEEE64.Finite; decide,
    by rw [hv]; norm_num, ?_⟩
  rw [hv]
  have hlo : (6369051672525773/4503599627370496 : ℝ)-1/1000000000000000 ≤ Real.sqrt 2 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hhi : Real.sqrt 2 ≤ (6369051672525773/4503599627370496 : ℝ)+1/1000000000000000 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> norm_num
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem attentionScore_error (q0 q1 k0 k1 : UInt64)
    (hq0 : Affine.Bounded q0 64) (hq1 : Affine.Bounded q1 64)
    (hk0 : Affine.Bounded k0 16) (hk1 : Affine.Bounded k1 16) :
    Approximation (attentionScore q0 q1 k0 k1)
      ((value q0*value k0+value q1*value k1)/Real.sqrt 2) 2051 (1/10000000000) := by
  have hd := Affine.dot2_error q0 q1 k0 k1 hq0 hq1 hk0 hk1
  have hp : |value q0*value k0+value q1*value k1| ≤ 2048 := by
    have h0 := mul_le_mul hq0.2 hk0.2 (abs_nonneg _) (by norm_num)
    have h1 := mul_le_mul hq1.2 hk1.2 (abs_nonneg _) (by norm_num)
    rw [← abs_mul] at h0 h1
    exact (abs_add_le _ _).trans (by linarith)
  have hs := hd.div_ge_one sqrtTwo_bounds.2 sqrtTwo_bounds.1
    ((Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)) hp
    (bound := 2050) (by norm_num) (by norm_num) (by norm_num)
  exact hs.weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])

#print axioms attentionScore_error
end Project.TinyGpt2
