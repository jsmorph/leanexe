import Project.LayerNorm.Real
import Project.ProofKit.RealNormBounds

namespace Project.LayerNorm.Real
open Project.ProofKit.RealNormalization

theorem normalized_sum (epsilon : ℝ) (x : Row) :
    (∑ i, normalized epsilon x i) = 0 := by
  simp [normalized, ← Finset.sum_div, centered, mean, Finset.sum_sub_distrib]
  left
  ring

theorem normalized_sumSquares (epsilon : ℝ) (he : 0 < epsilon) (x : Row) :
    sumSquares (normalized epsilon x) ≤ 4 := by
  have hr := deviation_pos epsilon he x
  have hs : sumSquares (normalized epsilon x) =
      sumSquares (centered x)/(deviation epsilon x)^2 := by
    simp only [sumSquares, normalized, div_pow, Finset.sum_div]
  rw [hs]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  rw [centered_sumSquares epsilon he x]
  linarith

theorem normalized_difference (epsilon : ℝ) (he : 0 < epsilon) (x y : Row) :
    sumSquares (fun i => normalized epsilon x i-normalized epsilon y i) ≤ 16 := by
  have hd := Project.ProofKit.RealNormBounds.difference
    (normalized epsilon x) (normalized epsilon y)
  linarith [normalized_sumSquares epsilon he x, normalized_sumSquares epsilon he y]

#print axioms normalized_sum
#print axioms normalized_sumSquares
#print axioms normalized_difference
end Project.LayerNorm.Real
