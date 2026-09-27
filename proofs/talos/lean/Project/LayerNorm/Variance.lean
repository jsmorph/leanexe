import Project.LayerNorm.Average

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem square_error_bounded (c : UInt64) (r bound targetBound error : ℝ)
    (hb : 1 ≤ bound) (hbmax : bound ≤ 64) (hc : Finite c)
    (bc : |value c| ≤ bound) (br : |r| ≤ targetBound) (he : |value c-r| ≤ error) :
    Finite (Wasm.IEEE64.mul c c) ∧
      |value (Wasm.IEEE64.mul c c)| ≤ bound^2+arithmeticEpsilon*bound^2 ∧
      |value (Wasm.IEEE64.mul c c)-r^2| ≤
        arithmeticEpsilon*bound^2+error*(bound+targetBound) := by
  have bs : |value c * value c| ≤ bound^2 := by
    rw [abs_mul]
    nlinarith only [bc, abs_nonneg (value c), hb]
  have hs := F64ArithmeticBounds.mul_error c c hc hc (bound^2) (by nlinarith)
    (by
      have h : bound^2 ≤ 4096 := by nlinarith
      exact h.trans_lt (by norm_num)) bs
  have hd : |value c * value c-r^2| ≤ error*(bound+targetBound) := by
    rw [show value c * value c-r^2 = (value c-r)*(value c+r) by ring, abs_mul]
    have hp := (abs_add_le _ _).trans (add_le_add bc br)
    exact mul_le_mul he hp (abs_nonneg _) ((abs_nonneg _).trans he)
  exact ⟨hs.1, F64ArithmeticBounds.magnitude_of_error _ _ _ _ hs.2 bs,
    (abs_sub_le _ _ _).trans (add_le_add hs.2 hd)⟩

theorem square_error (c : UInt64) (r : ℝ) (hc : Finite c)
    (bc : |value c| ≤ 12) (br : |r| ≤ 8) (he : |value c-r| ≤ 32*arithmeticEpsilon) :
    Finite (Wasm.IEEE64.mul c c) ∧ |value (Wasm.IEEE64.mul c c)| ≤ 145 ∧
      |value (Wasm.IEEE64.mul c c)-r^2| ≤ 784*arithmeticEpsilon := by
  have h := square_error_bounded c r 12 8 (32*arithmeticEpsilon)
    (by norm_num) (by norm_num) hc bc br he
  exact ⟨h.1, h.2.1.trans (by norm_num [arithmeticEpsilon]), h.2.2.trans_eq (by ring)⟩

theorem mean_perturbation (x y : Real.Row) (error : ℝ) (h : ∀ i, |x i-y i| ≤ error) :
    |Real.mean x - Real.mean y| ≤ error := by
  have heq : Real.mean x - Real.mean y = Real.mean (fun i => x i-y i) := by
    simp [Real.mean, Finset.sum_sub_distrib, sub_div]
  rw [heq]
  exact mean_magnitude _ error h

theorem variance_error_bounded (c : Fin 4 → UInt64) (r : Real.Row) (bound : ℝ)
    (hb : 1 ≤ bound) (hbmax : bound ≤ 16)
    (hf : ∀ i, Finite (c i)) (bc : ∀ i, |value (c i)| ≤ 3*bound)
    (br : ∀ i, |r i| ≤ 2*bound)
    (he : ∀ i, |value (c i)-r i| ≤ 8*bound*arithmeticEpsilon) :
    let v := average (Wasm.IEEE64.mul (c 0) (c 0)) (Wasm.IEEE64.mul (c 1) (c 1))
      (Wasm.IEEE64.mul (c 2) (c 2)) (Wasm.IEEE64.mul (c 3) (c 3))
    Finite v ∧ |value v| ≤ 4*bound^2+1 ∧
      |value v-RealNormalization.sumSquares r/4| ≤ (94*bound^2+5)*arithmeticEpsilon := by
  have hb2 : bound^2 ≤ 256 := by nlinarith
  have hs (i : Fin 4) := square_error_bounded (c i) (r i) (3*bound) (2*bound)
    (8*bound*arithmeticEpsilon) (by linarith) (by linarith) (hf i) (bc i) (br i) (he i)
  have hsMag (i : Fin 4) : |value (Wasm.IEEE64.mul (c i) (c i))| ≤ 9*bound^2+1 := by
    apply (hs i).2.1.trans
    have h := mul_le_mul_of_nonneg_left hb2 (by norm_num [arithmeticEpsilon] : 0 ≤ 9*arithmeticEpsilon)
    norm_num [arithmeticEpsilon] at *
    nlinarith
  have hsError (i : Fin 4) : |value (Wasm.IEEE64.mul (c i) (c i))-(r i)^2| ≤
      49*bound^2*arithmeticEpsilon := (hs i).2.2.trans_eq (by ring)
  have ha := average_error (fun i => Wasm.IEEE64.mul (c i) (c i)) (9*bound^2+1)
    (by nlinarith [sq_nonneg bound]) (by nlinarith) (fun i => (hs i).1) hsMag
  have hm := mean_perturbation (fun i => value (Wasm.IEEE64.mul (c i) (c i)))
    (fun i => (r i)^2) (49*bound^2*arithmeticEpsilon) hsError
  have herr : |value (average (Wasm.IEEE64.mul (c 0) (c 0)) (Wasm.IEEE64.mul (c 1) (c 1))
      (Wasm.IEEE64.mul (c 2) (c 2)) (Wasm.IEEE64.mul (c 3) (c 3))) -
        RealNormalization.sumSquares r / 4| ≤ (94*bound^2+5)*arithmeticEpsilon := by
    exact (abs_sub_le _ _ _).trans ((add_le_add ha.2.2 hm).trans_eq (by ring))
  refine ⟨ha.1, ?_, herr⟩
  have brs : |RealNormalization.sumSquares r / 4| ≤ 4*bound^2 := by
    apply mean_magnitude (fun i => (r i)^2) (4*bound^2)
    intro i
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := (sq_le_sq₀ (abs_nonneg (r i)) (by linarith : (0:ℝ) ≤ 2*bound)).mpr (br i)
    rw [sq_abs] at h
    nlinarith
  apply (F64ArithmeticBounds.magnitude_of_error _ _ _ _ herr brs).trans
  have h := mul_le_mul_of_nonneg_right hb2 F64ArithmeticBounds.epsilon_pos.le
  norm_num [arithmeticEpsilon] at *
  nlinarith

theorem variance_error (c : Fin 4 → UInt64) (r : Real.Row)
    (hf : ∀ i, Finite (c i)) (bc : ∀ i, |value (c i)| ≤ 12)
    (br : ∀ i, |r i| ≤ 8) (he : ∀ i, |value (c i)-r i| ≤ 32*arithmeticEpsilon) :
    let v := average (Wasm.IEEE64.mul (c 0) (c 0)) (Wasm.IEEE64.mul (c 1) (c 1))
      (Wasm.IEEE64.mul (c 2) (c 2)) (Wasm.IEEE64.mul (c 3) (c 3))
    Finite v ∧ |value v| ≤ 65 ∧
      |value v-RealNormalization.sumSquares r/4| ≤ 1536*arithmeticEpsilon := by
  have h := variance_error_bounded c r 4 (by norm_num) (by norm_num) hf
    (by convert bc using 1 <;> norm_num) (by convert br using 1 <;> norm_num)
    (by convert he using 1 <;> norm_num)
  exact ⟨h.1, h.2.1.trans_eq (by norm_num), h.2.2.trans (by norm_num [arithmeticEpsilon])⟩

#print axioms variance_error
end Project.LayerNorm
