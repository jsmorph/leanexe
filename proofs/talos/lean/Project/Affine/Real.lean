import Project.ProofKit.F64Approximation

namespace Project.Affine.Real

noncomputable def dot {ι : Type} [Fintype ι] (x w : ι → ℝ) : ℝ := ∑ i, x i*w i

theorem dot_magnitude {ι : Type} [Fintype ι] (x w : ι → ℝ) :
    |dot x w| ≤ ∑ i, |x i| * |w i| := by
  simpa only [dot, abs_mul] using Finset.abs_sum_le_sum_abs (fun i => x i*w i) Finset.univ

theorem product_perturbation (x y w v delta eta : ℝ)
    (hx : |x-y| ≤ delta) (hw : |w-v| ≤ eta) :
    |x*w-y*v| ≤ |w| * delta+|y| * eta := by
  rw [show x*w-y*v = w*(x-y)+y*(w-v) by ring]
  have h1 : |w*(x-y)| ≤ |w| * delta := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h2 : |y*(w-v)| ≤ |y| * eta := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem dot_perturbation {ι : Type} [Fintype ι]
    (x y w v delta eta : ι → ℝ)
    (hx : ∀ i, |x i-y i| ≤ delta i) (hw : ∀ i, |w i-v i| ≤ eta i) :
    |dot x w-dot y v| ≤ ∑ i, (|w i| * delta i+|y i| * eta i) := by
  rw [dot, dot, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => product_perturbation _ _ _ _ _ _ (hx i) (hw i)))

theorem dot_input_perturbation {ι : Type} [Fintype ι]
    (x y w : ι → ℝ) (delta : ℝ) (hx : ∀ i, |x i-y i| ≤ delta) :
    |dot x w-dot y w| ≤ (∑ i, |w i|)*delta := by
  have h := dot_perturbation x y w w (fun _ => delta) (fun _ => 0) hx (by simp)
  simpa only [mul_zero, add_zero, Finset.sum_mul] using h

theorem affine_perturbation {ι : Type} [Fintype ι]
    (x y w v delta eta : ι → ℝ) (b c theta : ℝ)
    (hx : ∀ i, |x i-y i| ≤ delta i) (hw : ∀ i, |w i-v i| ≤ eta i)
    (hb : |b-c| ≤ theta) :
    |(dot x w+b)-(dot y v+c)| ≤ (∑ i, (|w i| * delta i+|y i| * eta i))+theta := by
  rw [show (dot x w+b)-(dot y v+c) = (dot x w-dot y v)+(b-c) by ring]
  exact (abs_add_le _ _).trans (add_le_add (dot_perturbation x y w v delta eta hx hw) hb)

#print axioms affine_perturbation
end Project.Affine.Real
