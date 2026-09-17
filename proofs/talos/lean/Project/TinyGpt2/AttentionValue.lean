import Project.TinyGpt2.Model
import Project.Affine.Numerical
import Project.Softmax.Perturbation
import Project.Softmax.WeightedPerturbation
import Project.SoftmaxWide.Numerical

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem probability_output_bound (n a b c d : UInt64) (h : SoftmaxWide.Valid n a b c d)
    (i : Fin 4) : Affine.Bounded (Softmax.outputs (SoftmaxWide.compute n a b c d) i) 64 := by
  have hn := SoftmaxWide.compute_numerical n a b c d h
  have hp := SoftmaxWide.compute_nonnegative n a b c d h
  refine ⟨hn.1 i, ?_⟩
  rw [abs_of_nonneg (hp i)]
  have hi := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  have hs := (abs_le.mp hn.2.2).2
  have he : 52*arithmeticEpsilon ≤ (1:ℝ) := by norm_num [arithmeticEpsilon]
  linarith

theorem weightedValue_computed_error (p : Softmax.Result) (v : Fin 4 → UInt64)
    (hp : ∀ i, Affine.Bounded (Softmax.outputs p i) 64)
    (hv : ∀ i, Affine.Bounded (v i) 16)
    (target : Fin 4 → ℝ) (mass error : ℝ)
    (hn : ∀ i, 0 ≤ value (Softmax.outputs p i))
    (hm : ∑ i, value (Softmax.outputs p i) ≤ mass)
    (he : 0 ≤ error) (hvalue : ∀ i, |value (v i)-target i| ≤ error) :
    Finite (weightedValue p (v 0) (v 1) (v 2) (v 3)) ∧
      |value (weightedValue p (v 0) (v 1) (v 2) (v 3))-
        ∑ i, value (Softmax.outputs p i)*target i| ≤
          12294*arithmeticEpsilon+mass*error := by
  have hd := Affine.dot4_error (Softmax.outputs p) v hp hv
  have h := Affine.Real.dot_perturbation
    (fun i => value (Softmax.outputs p i)) (fun i => value (Softmax.outputs p i))
    (fun i => value (v i)) target (fun _ => 0) (fun _ => error) (by simp) hvalue
  simp only [mul_zero, zero_add, abs_of_nonneg (hn _), ← Finset.sum_mul] at h
  have ht := (abs_sub_le _ _ _).trans (add_le_add hd.accuracy h)
  exact ⟨hd.finite, ht.trans (add_le_add_right (mul_le_mul_of_nonneg_right hm he) _)⟩

theorem weightedValue_perturbed (n a b c d : UInt64) (h : SoftmaxWide.Valid n a b c d)
    (v : Fin 4 → UInt64) (hv : ∀ j, Affine.Bounded (v j) 16)
    (targetScores targetValues : Fin 4 → ℝ) (scoreError valueError valueBound : ℝ)
    (hs : 0 ≤ scoreError) (hb : 0 ≤ valueBound)
    (hvBound : ∀ j, |value (v j)| ≤ valueBound)
    (hscore : ∀ j, |value (Softmax.scores a b c d j)-targetScores j| ≤ scoreError)
    (hvalue : ∀ j, |value (v j)-targetValues j| ≤ valueError) :
    let output := weightedValue (SoftmaxWide.compute n a b c d) (v 0) (v 1) (v 2) (v 3)
    Finite output ∧
      |value output-∑ j, Softmax.Real.probability (Softmax.visible n) targetScores j*targetValues j| ≤
        12294*arithmeticEpsilon+valueBound*(10053*arithmeticEpsilon)+
          2*valueBound*scoreError+valueError := by
  let p := Softmax.outputs (SoftmaxWide.compute n a b c d)
  let scores := fun j => value (Softmax.scores a b c d j)
  let r := Softmax.Real.probability (Softmax.visible n) scores
  have hn := Affine.dot4_error p v (probability_output_bound n a b c d h) hv
  have hd := SoftmaxWide.compute_weighted_error n a b c d h (fun j => value (v j)) valueBound hb hvBound
  simp only [Softmax.reference_eq_real] at hd
  have ha := Softmax.Real.attention_perturbation (Softmax.visible n) scores targetScores
    (fun j => value (v j)) targetValues scoreError valueError valueBound
    ⟨0, by change decide ((0 : UInt64) < n) = true; exact decide_eq_true h.1⟩
    hs hb hscore hvBound hvalue
  have hlocal := (abs_sub_le _ _ _).trans (add_le_add hn.accuracy hd)
  have hall := (abs_sub_le _ _ _).trans (add_le_add hlocal ha)
  exact ⟨hn.finite, hall.trans (by ring_nf; rfl)⟩

#print axioms weightedValue_perturbed
end Project.TinyGpt2
