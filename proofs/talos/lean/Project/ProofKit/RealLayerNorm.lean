import Project.ProofKit.RealNormalization

namespace Project.ProofKit.RealLayerNorm
open RealNormalization

noncomputable def mean {n : Nat} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n
noncomputable def centered {n : Nat} (x : Fin n → ℝ) (i : Fin n) : ℝ := x i - mean x
noncomputable def variance {n : Nat} (x : Fin n → ℝ) : ℝ := sumSquares (centered x) / n
noncomputable def deviation {n : Nat} (epsilon : ℝ) (x : Fin n → ℝ) : ℝ := Real.sqrt (variance x + epsilon)
noncomputable def normalized {n : Nat} (epsilon : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  centered x i / deviation epsilon x

theorem sum_eq_mean {n : Nat} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, x i = (n : ℝ) * mean x := by
  unfold mean
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  field_simp [hnReal]

theorem mean_sub {n : Nat} (x y : Fin n → ℝ) :
    mean (fun i => x i - y i) = mean x - mean y := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem centered_sumSquares {n : Nat} (hn : 0 < n) (x : Fin n → ℝ) :
    sumSquares (centered x) = sumSquares x - n * (mean x) ^ 2 := by
  have hMean := sum_eq_mean hn x
  calc
    sumSquares (centered x) = sumSquares x - 2 * mean x * (∑ i, x i) + n * (mean x) ^ 2 := by
      simp only [sumSquares, centered, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [hMean]; ring

theorem centering_distance {n : Nat} (hn : 0 < n) (x y : Fin n → ℝ) :
    squaredDistance (centered x) (centered y) ≤ squaredDistance x y := by
  have hCenter : (fun i => centered x i - centered y i) = centered (fun i => x i - y i) := by
    funext i
    simp only [centered, mean_sub]
    ring
  rw [squaredDistance, hCenter, centered_sumSquares hn]
  exact sub_le_self _ (by positivity)

theorem variance_nonneg {n : Nat} (x : Fin n → ℝ) : 0 ≤ variance x :=
  div_nonneg (sumSquares_nonneg _) (Nat.cast_nonneg _)

theorem deviation_pos {n : Nat} (epsilon : ℝ) (he : 0 < epsilon) (x : Fin n → ℝ) :
    0 < deviation epsilon x :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (variance_nonneg x) he)

theorem normalization_sumSquares {n : Nat} (hn : 0 < n) (epsilon : ℝ) (he : 0 < epsilon)
    (x : Fin n → ℝ) :
    sumSquares (centered x) = n * ((deviation epsilon x) ^ 2 - epsilon) := by
  have hSq := Real.sq_sqrt (add_nonneg (variance_nonneg x) he.le)
  change (deviation epsilon x) ^ 2 = variance x + epsilon at hSq
  rw [hSq, add_sub_cancel_right, variance]
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  field_simp [hnReal]

theorem component_perturbation {n : Nat} (hn : 0 < n)
    (epsilon delta lower : ℝ) (he : 0 < epsilon) (hd : 0 ≤ delta) (hl : 0 < lower)
    (x y : Fin n → ℝ) (hx : lower ≤ deviation epsilon x) (hy : lower ≤ deviation epsilon y)
    (hxy : ∀ i, |x i - y i| ≤ delta) (i : Fin n) :
    |normalized epsilon x i - normalized epsilon y i| ≤ Real.sqrt n * delta / lower := by
  have hDistance : squaredDistance x y ≤ (Real.sqrt n * delta) ^ 2 := by
    calc
      squaredDistance x y ≤ ∑ _ : Fin n, delta ^ 2 := by
        unfold squaredDistance sumSquares
        exact Finset.sum_le_sum (fun j _ => by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd).mpr (hxy j))
      _ = (Real.sqrt n * delta) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  exact normalization_component_error (centered x) (centered y)
    (deviation epsilon x) (deviation epsilon y) epsilon n lower (Real.sqrt n * delta)
    (deviation_pos epsilon he x) (deviation_pos epsilon he y) he.le (Nat.cast_nonneg _)
    hl (by positivity) hx hy (normalization_sumSquares hn epsilon he x)
    (normalization_sumSquares hn epsilon he y) ((centering_distance hn x y).trans hDistance) i

#print axioms centering_distance
#print axioms component_perturbation
end Project.ProofKit.RealLayerNorm
