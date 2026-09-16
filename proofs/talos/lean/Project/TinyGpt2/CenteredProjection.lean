import Project.TinyGpt2.Real
import Project.TinyGpt2.ScoreRange

namespace Project.TinyGpt2.Real
open Project.ProofKit.RealNormBounds

noncomputable def centeredColumn (w : Row) : Row :=
  fun i => w i-(∑ j, w j)/4

theorem affine_projection_centered (g b z w : Row) (hz : ∑ i, z i = 0) :
    (∑ i, (z i*g i+b i)*w i) =
      (∑ i, z i*centeredColumn (fun j => g j*w j) i)+(∑ i, b i*w i) := by
  rw [show (∑ i, z i*centeredColumn (fun j => g j*w j) i) =
    ∑ i, z i*(g i*w i) from dot_center z _ _ hz]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc]

theorem bilinear_projection {n : Nat} (a b : Matrix 4 n) (z u : Row) (c : Fin n → ℝ) :
    (∑ h, ((∑ i, z i*a i h)+c h)*(∑ j, u j*b j h)) =
      (∑ i, ∑ j, z i*(∑ h, a i h*b j h)*u j)+
        (∑ j, (∑ h, c h*b j h)*u j) := by
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro h _
    ring
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro h _
    ring

#print axioms affine_projection_centered
#print axioms bilinear_projection
end Project.TinyGpt2.Real
