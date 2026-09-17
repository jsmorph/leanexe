import Project.TinyGpt2.Model
import Project.Affine.Numerical
import Project.Softmax.Perturbation
import Project.Softmax.RealProperties

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem probability_output_bound (n a b c d : UInt64) (h : Softmax.SpreadValid n a b c d)
    (i : Fin 4) : Affine.Bounded (Softmax.outputs (Softmax.compute n a b c d) i) 64 := by
  have hn := Softmax.compute_numerical_spread n a b c d h
  refine ⟨(hn.2.1 i).1, ?_⟩
  rw [abs_of_nonneg (hn.2.1 i).2.1]
  have hi := Finset.single_le_sum (fun j _ => (hn.2.1 j).2.1) (Finset.mem_univ i)
  have hs := (abs_le.mp hn.2.2).2
  have he : 32*arithmeticEpsilon ≤ (1:ℝ) := by norm_num [arithmeticEpsilon]
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

theorem weightedValue_perturbed (n a b c d : UInt64) (h : Softmax.SpreadValid n a b c d)
    (v : Fin 4 → UInt64) (hv : ∀ j, Affine.Bounded (v j) 16)
    (targetScores targetValues : Fin 4 → ℝ) (scoreError valueError : ℝ)
    (hs : 0 ≤ scoreError)
    (hscore : ∀ j, |value (Softmax.scores a b c d j)-targetScores j| ≤ scoreError)
    (hvalue : ∀ j, |value (v j)-targetValues j| ≤ valueError) :
    let output := weightedValue (Softmax.compute n a b c d) (v 0) (v 1) (v 2) (v 3)
    Finite output ∧
      |value output-∑ j, Softmax.Real.probability (Softmax.visible n) targetScores j*targetValues j| ≤
        1/10000000000+(∑ j, |value (v j)|)*(1/50000+2*scoreError)+valueError := by
  let p := Softmax.outputs (Softmax.compute n a b c d)
  let r := Softmax.Real.probability (Softmax.visible n) targetScores
  have hn := Affine.dot4_error p v (probability_output_bound n a b c d h) hv
  have hp : ∀ j, |value (p j)-r j| ≤ 1/50000+2*scoreError :=
    Softmax.compute_spread_perturbed n a b c d h targetScores scoreError hs hscore
  have hd := Affine.Real.dot_perturbation (fun j => value (p j)) r (fun j => value (v j))
    targetValues (fun _ => 1/50000+2*scoreError) (fun _ => valueError) hp hvalue
  have hr : ∑ j, |r j| = 1 := by
    have hrn (j : Fin 4) : 0 ≤ r j :=
      Softmax.Real.probability_nonnegative (Softmax.visible n) targetScores j
    simp_rw [abs_of_nonneg (hrn _)]
    exact Softmax.Real.probability_sum (Softmax.visible n) targetScores
      ⟨0, by change decide ((0 : UInt64) < n) = true; exact decide_eq_true h.1⟩
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hr, one_mul] at hd
  have herr := (abs_sub_le _ _ _).trans (add_le_add hn.accuracy hd)
  refine ⟨hn.finite, ?_⟩
  have hlocal : 12294*arithmeticEpsilon ≤ (1:ℝ)/10000000000 := by norm_num [arithmeticEpsilon]
  exact herr.trans (by linarith)

#print axioms weightedValue_perturbed
end Project.TinyGpt2
