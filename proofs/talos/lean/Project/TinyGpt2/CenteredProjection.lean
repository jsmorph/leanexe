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

theorem normalized_projection (p : NormParameters) (x w : Row) :
    (∑ i, norm p x i*w i) =
      (∑ i, LayerNorm.Real.normalized (1/100000) x i*
        centeredColumn (fun j => p.scale j*w j) i)+(∑ i, p.bias i*w i) := by
  exact affine_projection_centered p.scale p.bias
    (LayerNorm.Real.normalized (1/100000) x) w
    (LayerNorm.Real.normalized_sum _ _)

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

noncomputable def centeredHead (p : NormParameters) (w : Matrix 4 4)
    (head : Fin 2) : Matrix 4 2 :=
  fun i k => centeredColumn (fun j => p.scale j*w j (coordinate head k)) i

noncomputable def projectedBias (p : NormParameters) (w : Matrix 4 4)
    (head k : Fin 2) : ℝ := ∑ i, p.bias i*w i (coordinate head k)

noncomputable def scoreMatrix (p : Parameters) (head : Fin 2) : Matrix 4 4 :=
  fun i j => ∑ k, centeredHead p.norm1 p.query head i k*
    centeredHead p.norm1 p.key head j k

noncomputable def scoreLinear (p : Parameters) (head : Fin 2) : Row :=
  fun j => ∑ k, projectedBias p.norm1 p.query head k*centeredHead p.norm1 p.key head j k

noncomputable def rowScore (p : Parameters) (x y : Row) (head : Fin 2) : ℝ :=
  (∑ k, matrixApply p.query (norm p.norm1 x) (coordinate head k)*
    matrixApply p.key (norm p.norm1 y) (coordinate head k))/Real.sqrt 2

theorem row_score_difference_centered (p : Parameters) (x y v : Row) (head : Fin 2) :
    rowScore p x y head-rowScore p x v head =
      let z := LayerNorm.Real.normalized (1/100000) x
      let u := fun a => LayerNorm.Real.normalized (1/100000) y a-
        LayerNorm.Real.normalized (1/100000) v a
      ((∑ a, ∑ b, z a*scoreMatrix p head a b*u b)+
        (∑ b, scoreLinear p head b*u b))/Real.sqrt 2 := by
  let z := LayerNorm.Real.normalized (1/100000) x
  let u := fun a => LayerNorm.Real.normalized (1/100000) y a-
    LayerNorm.Real.normalized (1/100000) v a
  have hproj (r : Row) (w : Matrix 4 4) (k : Fin 2) :
      matrixApply w (norm p.norm1 r) (coordinate head k) =
        (∑ a, LayerNorm.Real.normalized (1/100000) r a*
          centeredHead p.norm1 w head a k)+projectedBias p.norm1 w head k :=
    normalized_projection p.norm1 _ _
  unfold rowScore
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp_rw [hproj, ← mul_sub, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib,
    ← sub_mul]
  exact congrArg (fun r : ℝ => r/Real.sqrt 2)
    (bilinear_projection (centeredHead p.norm1 p.query head)
      (centeredHead p.norm1 p.key head) z u (projectedBias p.norm1 p.query head))

theorem row_score_spread_bound (p : Parameters) (x y v : Row) (head : Fin 2)
    (hw : (∑ a, Project.ProofKit.RealNormalization.sumSquares (scoreMatrix p head a)) ≤ 144/25)
    (hd : Project.ProofKit.RealNormalization.sumSquares (scoreLinear p head) ≤ 49/400) :
    |rowScore p x y head-rowScore p x v head| ≤ 103/7 := by
  rw [row_score_difference_centered]
  apply centered_score_bound _ _ _ _ hw hd
  · exact LayerNorm.Real.normalized_sumSquares _ (by norm_num) _
  · exact LayerNorm.Real.normalized_difference _ (by norm_num) _ _

theorem score_spread_bound (p : Parameters) (tokens : Tokens) (i : Fin 4) (head : Fin 2)
    (hw : (∑ a, Project.ProofKit.RealNormalization.sumSquares (scoreMatrix p head a)) ≤ 144/25)
    (hd : Project.ProofKit.RealNormalization.sumSquares (scoreLinear p head) ≤ 49/400)
    (j l : Fin 4) : |score p tokens i head j-score p tokens i head l| ≤ 103/7 :=
  row_score_spread_bound p (embedding p tokens i) (embedding p tokens j)
    (embedding p tokens l) head hw hd

#print axioms affine_projection_centered
#print axioms bilinear_projection
#print axioms row_score_difference_centered
#print axioms score_spread_bound
end Project.TinyGpt2.Real
