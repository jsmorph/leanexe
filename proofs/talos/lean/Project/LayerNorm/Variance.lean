import Project.LayerNorm.Average

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem square_error (c : UInt64) (r : ℝ) (hc : Finite c)
    (bc : |value c| ≤ 12) (br : |r| ≤ 8) (he : |value c-r| ≤ 32*arithmeticEpsilon) :
    Finite (Wasm.IEEE64.mul c c) ∧ |value (Wasm.IEEE64.mul c c)| ≤ 145 ∧
      |value (Wasm.IEEE64.mul c c)-r^2| ≤ 784*arithmeticEpsilon := by
  have bs : |value c * value c| ≤ 144 := by
    rw [abs_mul]
    nlinarith only [bc, abs_nonneg (value c)]
  have hs := F64ArithmeticBounds.mul_error c c hc hc 144 (by norm_num) (by norm_num) bs
  have hd : |value c * value c - r^2| ≤ 640*arithmeticEpsilon := by
    rw [show value c * value c-r^2 = (value c-r)*(value c+r) by ring, abs_mul]
    have hp : |value c+r| ≤ 20 := (abs_add_le _ _).trans (by linarith only [bc, br])
    exact (mul_le_mul he hp (abs_nonneg _) (by positivity [F64ArithmeticBounds.epsilon_pos])).trans_eq (by ring)
  refine ⟨hs.1, ?_, ?_⟩
  · exact (F64ArithmeticBounds.magnitude_of_error _ _ _ 144 hs.2 bs).trans
      (by norm_num [arithmeticEpsilon])
  · exact (abs_sub_le _ _ _).trans ((add_le_add hs.2 hd).trans_eq (by ring))

theorem mean_perturbation (x y : Real.Row) (error : ℝ) (h : ∀ i, |x i-y i| ≤ error) :
    |Real.mean x - Real.mean y| ≤ error := by
  have heq : Real.mean x - Real.mean y = Real.mean (fun i => x i-y i) := by
    simp [Real.mean, Finset.sum_sub_distrib, sub_div]
  rw [heq]
  exact mean_magnitude _ error h

theorem variance_error (c : Fin 4 → UInt64) (r : Real.Row)
    (hf : ∀ i, Finite (c i)) (bc : ∀ i, |value (c i)| ≤ 12)
    (br : ∀ i, |r i| ≤ 8) (he : ∀ i, |value (c i)-r i| ≤ 32*arithmeticEpsilon) :
    let v := average (Wasm.IEEE64.mul (c 0) (c 0)) (Wasm.IEEE64.mul (c 1) (c 1))
      (Wasm.IEEE64.mul (c 2) (c 2)) (Wasm.IEEE64.mul (c 3) (c 3))
    Finite v ∧ |value v| ≤ 65 ∧
      |value v - RealNormalization.sumSquares r / 4| ≤ 1536*arithmeticEpsilon := by
  have hs (i : Fin 4) := square_error (c i) (r i) (hf i) (bc i) (br i) (he i)
  have ha := average_error (fun i => Wasm.IEEE64.mul (c i) (c i)) 145
    (by norm_num) (by norm_num) (fun i => (hs i).1) (fun i => (hs i).2.1)
  have hm := mean_perturbation (fun i => value (Wasm.IEEE64.mul (c i) (c i)))
    (fun i => (r i)^2) (784*arithmeticEpsilon) (fun i => (hs i).2.2)
  have herr : |value (average (Wasm.IEEE64.mul (c 0) (c 0)) (Wasm.IEEE64.mul (c 1) (c 1))
      (Wasm.IEEE64.mul (c 2) (c 2)) (Wasm.IEEE64.mul (c 3) (c 3))) -
        RealNormalization.sumSquares r / 4| ≤ 1536*arithmeticEpsilon := by
    exact (abs_sub_le _ _ _).trans ((add_le_add ha.2.2 hm).trans
      (by norm_num [arithmeticEpsilon]))
  refine ⟨ha.1, ?_, herr⟩
  have brs : |RealNormalization.sumSquares r / 4| ≤ 64 := by
    apply mean_magnitude (fun i => (r i)^2) 64
    intro i
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := (sq_le_sq₀ (abs_nonneg (r i)) (by norm_num : (0:ℝ) ≤ 8)).mpr (br i)
    simpa only [sq_abs, show (8:ℝ)^2 = 64 by norm_num] using h
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ 64 herr brs).trans
    (by norm_num [arithmeticEpsilon])

#print axioms variance_error
end Project.LayerNorm
