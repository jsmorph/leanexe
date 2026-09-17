import Project.ProofKit.F64ArithmeticBounds

namespace Project.ProofKit.F64Square
open CodeLib.IEEE64 F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem relative_approximation (word : UInt64) (r k : ℝ)
    (hf : Finite word) (hr : 0 < r) (hu : r ≤ 1)
    (hk : 0 ≤ k) (hkmax : k ≤ 10000) (hmin : minNormal64 ≤ 2*r^2)
    (he : |value word-r| ≤ k*arithmeticEpsilon*r) :
    Finite (Wasm.IEEE64.mul word word) ∧
      |value (Wasm.IEEE64.mul word word)-r^2| ≤ (2*k+3)*arithmeticEpsilon*r^2 := by
  let d := k*arithmeticEpsilon
  have hd0 : 0 ≤ d := mul_nonneg hk epsilon_pos.le
  have hd : d ≤ 1/100 := by
    dsimp [d]
    have hm := mul_le_mul_of_nonneg_right hkmax epsilon_pos.le
    norm_num [arithmeticEpsilon] at hm ⊢
    linarith only [hm]
  have hd2 : d^2 ≤ arithmeticEpsilon := by
    have hksq : k^2 ≤ 10000^2 := pow_le_pow_left₀ hk hkmax 2
    have hm := mul_le_mul_of_nonneg_right hksq (sq_nonneg arithmeticEpsilon)
    dsimp [d]
    nlinarith only [hm, show 10000^2*arithmeticEpsilon^2 ≤ arithmeticEpsilon by
      norm_num [arithmeticEpsilon]]
  have hw : |value word| ≤ r+d*r := by
    exact magnitude_of_error _ _ _ _ he (by rw [abs_of_pos hr])
  have hprod : |value word*value word| ≤ 2*r^2 := by
    rw [abs_mul]
    have hm := mul_le_mul hw hw (abs_nonneg _) (by positivity)
    have hf : (1+d)^2 ≤ 2 := by nlinarith only [hd0, hd]
    have hs := mul_le_mul_of_nonneg_right hf (sq_nonneg r)
    nlinarith only [hm, hs]
  have hm := mul_error_scaled word word hf hf (2*r^2) hmin
    (by have hr2 : r^2 ≤ 1 := pow_le_one₀ hr.le hu
        exact (show 2*r^2 ≤ 2 by linarith).trans_lt (by norm_num)) hprod
  have hsum : |value word+r| ≤ (2+d)*r := by
    have ht := abs_add_le (value word) r
    rw [abs_of_pos hr] at ht
    linarith only [ht, hw]
  have hp : |value word*value word-r^2| ≤ (2*d+d^2)*r^2 := by
    rw [show value word*value word-r^2 = (value word-r)*(value word+r) by ring, abs_mul]
    calc
      _ ≤ (d*r)*((2+d)*r) := mul_le_mul he hsum (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hb := mul_le_mul_of_nonneg_right hd2 (sq_nonneg r)
  refine ⟨hm.1, (abs_sub_le _ _ _).trans ((add_le_add hm.2 hp).trans ?_)⟩
  dsimp [d] at *
  nlinarith only [hb]

#print axioms relative_approximation
end Project.ProofKit.F64Square
