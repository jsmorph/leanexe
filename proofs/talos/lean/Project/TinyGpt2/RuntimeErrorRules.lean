import Project.TinyGpt2.RuntimeAffine
import Project.TinyGpt2.RuntimeScore
import Project.TinyGpt2.RuntimeAttention

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem dotColumn4_error_perturbed (w : Array UInt64) (offset width : Nat) (j : Fin width)
    (x : Row) (target : Real.Row) (inputBound weightBound error : ℝ)
    (hx0 : 0 ≤ inputBound) (hw0 : 0 ≤ weightBound) (he : 0 ≤ error)
    (hmax : inputBound*weightBound+1 ≤ 2^40)
    (hx : ∀ i, Affine.Bounded (rowWords x i) inputBound)
    (hw : ∀ i k, Affine.Bounded (matrixWords w offset 4 width i k) weightBound)
    (herror : ∀ i, |decodeRow x i-target i| ≤ error) :
    Approximation (dotColumn4 w offset width j.val x)
      (Real.matrixApply (decodeMatrix w offset 4 width) target j)
      (4*(inputBound*weightBound+1)+5)
      ((12*(inputBound*weightBound+1)+6)*arithmeticEpsilon+4*weightBound*error) := by
  have hn := dotColumn4_error_wide w offset width j x inputBound weightBound hx0 hw0 hmax hx
    (fun i => hw i j)
  have hp := matrix_input_error (decodeMatrix w offset 4 width) (decodeRow x) target weightBound error
    he (fun i k => (hw i k).2) herror j
  exact ⟨hn.finite, hn.magnitude, (abs_sub_le _ _ _).trans (add_le_add hn.accuracy hp)⟩

theorem dotColumn8_error_perturbed (w : Array UInt64) (offset width : Nat) (j : Fin width)
    (x : WideRow) (target : Fin 8 → ℝ) (inputBound weightBound error : ℝ)
    (hx0 : 0 ≤ inputBound) (hw0 : 0 ≤ weightBound) (he : 0 ≤ error)
    (hmax : inputBound*weightBound+1 ≤ 2^40)
    (hx : ∀ i, Affine.Bounded (wideWords x i) inputBound)
    (hw : ∀ i k, Affine.Bounded (matrixWords w offset 8 width i k) weightBound)
    (herror : ∀ i, |value (wideWords x i)-target i| ≤ error) :
    Approximation (dotColumn8 w offset width j.val x)
      (Real.matrixApply (decodeMatrix w offset 8 width) target j)
      (8*(inputBound*weightBound+1)+11)
      ((32*(inputBound*weightBound+1)+22)*arithmeticEpsilon+8*weightBound*error) := by
  have hn := dotColumn8_error_wide w offset width j x inputBound weightBound hx0 hw0 hmax hx
    (fun i => hw i j)
  have hp := matrix_input_error (decodeMatrix w offset 8 width) (fun i => value (wideWords x i))
    target weightBound error he (fun i k => (hw i k).2) herror j
  exact ⟨hn.finite, hn.magnitude, (abs_sub_le _ _ _).trans (add_le_add hn.accuracy hp)⟩

theorem add_accuracy (x y : UInt64) (p q bound ex ey : ℝ)
    (hb1 : 1 ≤ bound) (hbMax : bound ≤ 2^40) (hx : Finite x) (hy : Finite y)
    (hs : |value x+value y| ≤ bound)
    (hex : |value x-p| ≤ ex) (hey : |value y-q| ≤ ey) :
    |value (Wasm.IEEE64.add x y)-(p+q)| ≤ bound*arithmeticEpsilon+ex+ey := by
  have hn := add_error_wide x y bound hb1 hbMax hx hy hs
  have hp : |value x+value y-(p+q)| ≤ ex+ey := by
    rw [show value x+value y-(p+q) = (value x-p)+(value y-q) by ring]
    exact (abs_add_le _ _).trans (add_le_add hex hey)
  exact (abs_sub_le _ _ _).trans ((add_le_add hn.accuracy hp).trans_eq (by ring))

theorem attentionScore_accuracy (q0 q1 k0 k1 : UInt64) (p0 p1 r0 r1 bound realBound error : ℝ)
    (hb1 : 1 ≤ bound^2) (hbMax : bound^2 ≤ 2^40) (he : 0 ≤ error)
    (hq0 : Affine.Bounded q0 bound) (hq1 : Affine.Bounded q1 bound)
    (hk0 : Affine.Bounded k0 bound) (hk1 : Affine.Bounded k1 bound)
    (hp0 : |p0| ≤ realBound) (hp1 : |p1| ≤ realBound)
    (heq0 : |value q0-p0| ≤ error) (heq1 : |value q1-p1| ≤ error)
    (hek0 : |value k0-r0| ≤ error) (hek1 : |value k1-r1| ≤ error) :
    |value (attentionScore q0 q1 k0 k1)-(p0*r0+p1*r1)/Real.sqrt 2| ≤
      (16*bound^2+3)*arithmeticEpsilon+2*(bound+realBound)*error := by
  have hb0 : 0 ≤ bound := (abs_nonneg _).trans hq0.2
  have hprod (q k : UInt64) (hq : Affine.Bounded q bound) (hk : Affine.Bounded k bound) :
      |value q*value k| ≤ bound^2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hq.2 hk.2 (abs_nonneg _) hb0
  have hn := attentionScore_error_wide q0 q1 k0 k1 (bound^2) hb1 hbMax
    hq0.1 hq1.1 hk0.1 hk1.1 (hprod _ _ hq0 hk0) (hprod _ _ hq1 hk1)
  have h0 := Affine.Real.product_perturbation (value q0) p0 (value k0) r0 error error heq0 hek0
  have h1 := Affine.Real.product_perturbation (value q1) p1 (value k1) r1 error error heq1 hek1
  have h0' := h0.trans (add_le_add (mul_le_mul_of_nonneg_right hk0.2 he)
    (mul_le_mul_of_nonneg_right hp0 he))
  have h1' := h1.trans (add_le_add (mul_le_mul_of_nonneg_right hk1.2 he)
    (mul_le_mul_of_nonneg_right hp1 he))
  have hs : |(value q0*value k0+value q1*value k1)-(p0*r0+p1*r1)| ≤
      2*(bound+realBound)*error := by
    rw [show (value q0*value k0+value q1*value k1)-(p0*r0+p1*r1) =
      (value q0*value k0-p0*r0)+(value q1*value k1-p1*r1) by ring]
    exact (abs_add_le _ _).trans ((add_le_add h0' h1').trans_eq (by ring))
  have hd : (1:ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hp : |(value q0*value k0+value q1*value k1)/Real.sqrt 2-(p0*r0+p1*r1)/Real.sqrt 2| ≤
      2*(bound+realBound)*error := by
    rw [← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt 2)).mpr
    exact hs.trans (le_mul_of_one_le_right ((abs_nonneg _).trans hs) hd)
  exact (abs_sub_le _ _ _).trans (add_le_add hn.accuracy hp)

theorem weightedValue_accuracy (n a b c d : UInt64) (h : SoftmaxWide.Valid n a b c d)
    (v : Fin 4 → UInt64) (targetScores targetValues : Fin 4 → ℝ)
    (bound scoreError valueError : ℝ) (hb1 : 1 ≤ bound) (hbMax : bound ≤ 2^30)
    (hs : 0 ≤ scoreError) (hv : ∀ i, Affine.Bounded (v i) bound)
    (hscore : ∀ i, |value (Softmax.scores a b c d i)-targetScores i| ≤ scoreError)
    (hvalue : ∀ i, |value (v i)-targetValues i| ≤ valueError) :
    |value (weightedValue (SoftmaxWide.compute n a b c d) (v 0) (v 1) (v 2) (v 3))-
      ∑ i, Softmax.Real.probability (Softmax.visible n) targetScores i*targetValues i| ≤
        (10077*bound+6)*arithmeticEpsilon+2*bound*scoreError+valueError := by
  have hn := weightedValue_error_wide n a b c d h v bound hb1 hbMax hv
  have hp := Softmax.Real.attention_perturbation (Softmax.visible n)
    (fun i => value (Softmax.scores a b c d i)) targetScores
    (fun i => value (v i)) targetValues scoreError valueError bound
    ⟨0, by change decide ((0 : UInt64) < n) = true; exact decide_eq_true h.1⟩
    hs (by linarith) hscore (fun i => (hv i).2) hvalue
  simp only [Softmax.reference_eq_real] at hn
  exact (abs_sub_le _ _ _).trans ((add_le_add hn.accuracy hp).trans_eq (by ring))

#print axioms attentionScore_accuracy
#print axioms weightedValue_accuracy
end Project.TinyGpt2
