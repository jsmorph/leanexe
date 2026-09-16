import Project.TinyGpt2.CenteredProjection

namespace Project.TinyGpt2.Real
open Project.ProofKit RealNormalization RealNormBounds

theorem normalized_projection_bound (p : NormParameters) (x w : Row) (a b : ℝ)
    (ha : 0 ≤ a)
    (hw : sumSquares (centeredColumn (fun i => p.scale i*w i)) ≤ a^2)
    (hb : |∑ i, p.bias i*w i| ≤ b) :
    |∑ i, norm p x i*w i| ≤ 2*a+b := by
  rw [normalized_projection]
  have hd := dot (LayerNorm.Real.normalized (1/100000) x)
    (centeredColumn (fun i => p.scale i*w i)) 2 a (by norm_num) ha
    (by convert LayerNorm.Real.normalized_sumSquares (1/100000) (by norm_num) x using 1 <;> norm_num) hw
  exact (abs_add_le _ _).trans (add_le_add hd hb)

noncomputable def headOutputColumn (v a : Matrix 4 4) (head : Fin 2) (j : Fin 4) : Row :=
  fun i => ∑ k, v i (coordinate head k)*a (coordinate head k) j

theorem head_output_projection (v a : Matrix 4 4) (x : Row) (head : Fin 2) (j : Fin 4) :
    (∑ k, matrixApply v x (coordinate head k)*a (coordinate head k) j) =
      ∑ i, x i*headOutputColumn v a head j i := by
  simp only [matrixApply, headOutputColumn, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem weighted_magnitude {n : Nat} (p x : Fin n → ℝ) (mass bound : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hm : ∑ i, p i ≤ mass)
    (hb : 0 ≤ bound) (hx : ∀ i, |x i| ≤ bound) :
    |∑ i, p i*x i| ≤ mass*bound := by
  calc
    _ ≤ ∑ i, |p i*x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i*|x i| := by simp only [abs_mul, abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i*bound := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hp i))
    _ = (∑ i, p i)*bound := (Finset.sum_mul _ _ _).symm
    _ ≤ mass*bound := mul_le_mul_of_nonneg_right hm hb

theorem sum_four_heads (f : Fin 4 → ℝ) :
    (∑ i, f i) = ∑ h, ∑ k, f (coordinate h k) := by
  simp [Fin.sum_univ_succ, coordinate]
  ring

theorem headOf_coordinate (head k : Fin 2) : headOf (coordinate head k) = head := by
  fin_cases head <;> fin_cases k <;> rfl

theorem attention_projection_group (p : Fin 2 → Fin 4 → ℝ) (v : Fin 4 → Row)
    (a : Matrix 4 4) (j : Fin 4) :
    matrixApply a (fun k => ∑ i, p (headOf k) i*v i k) j =
      ∑ head, ∑ i, p head i*(∑ k, v i (coordinate head k)*a (coordinate head k) j) := by
  rw [matrixApply, sum_four_heads]
  simp_rw [headOf_coordinate, Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro head _
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

#print axioms normalized_projection_bound
#print axioms weighted_magnitude
end Project.TinyGpt2.Real
