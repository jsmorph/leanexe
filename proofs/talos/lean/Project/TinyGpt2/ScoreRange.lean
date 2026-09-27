import Project.LayerNorm.Structural

namespace Project.TinyGpt2
open Project.ProofKit.RealNormalization Project.ProofKit.RealNormBounds

theorem centered_score_bound (w : Fin 4 → Fin 4 → ℝ) (d z u : Fin 4 → ℝ)
    (hw : (∑ i, sumSquares (w i)) ≤ 144/25) (hd : sumSquares d ≤ 49/400)
    (hz : sumSquares z ≤ 4) (hu : sumSquares u ≤ 16) :
    |((∑ i, ∑ j, z i*w i j*u j)+(∑ i, d i*u i))/Real.sqrt 2| ≤ 103/7 := by
  have hm := bilinear w z u 2 (12/5) 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact hz) (by norm_num; exact hw) (by norm_num; exact hu)
  have hl := dot d u (7/20) 4 (by norm_num) (by norm_num)
    (by norm_num; exact hd) (by norm_num; exact hu)
  have hs : (7:ℝ)/5 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp : (0:ℝ) < Real.sqrt 2 := by positivity
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hsum := (abs_add_le _ _).trans (add_le_add hm hl)
  nlinarith

#print axioms centered_score_bound
end Project.TinyGpt2
