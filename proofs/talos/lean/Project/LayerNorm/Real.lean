import Project.ProofKit.RealNormalization

namespace Project.LayerNorm.Real
open Project.ProofKit.RealNormalization

abbrev Row := Fin 4 → ℝ

noncomputable def mean (x : Row) : ℝ := (∑ i, x i) / 4
noncomputable def centered (x : Row) (i : Fin 4) : ℝ := x i - mean x
noncomputable def variance (x : Row) : ℝ := sumSquares (centered x) / 4
noncomputable def deviation (epsilon : ℝ) (x : Row) : ℝ := Real.sqrt (variance x + epsilon)
noncomputable def normalized (epsilon : ℝ) (x : Row) (i : Fin 4) : ℝ :=
  centered x i / deviation epsilon x
noncomputable def layerNorm (epsilon : ℝ) (x gamma beta : Row) (i : Fin 4) : ℝ :=
  normalized epsilon x i * gamma i + beta i

theorem variance_nonneg (x : Row) : 0 ≤ variance x :=
  div_nonneg (sumSquares_nonneg _) (by norm_num)

theorem deviation_pos (epsilon : ℝ) (he : 0 < epsilon) (x : Row) :
    0 < deviation epsilon x :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (variance_nonneg x) he)

theorem deviation_lower (epsilon : ℝ) (x : Row) :
    Real.sqrt epsilon ≤ deviation epsilon x :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_left (variance_nonneg x))

theorem centered_sumSquares (epsilon : ℝ) (he : 0 < epsilon) (x : Row) :
    sumSquares (centered x) = 4 * ((deviation epsilon x)^2 - epsilon) := by
  have hs := Real.sq_sqrt (add_nonneg (variance_nonneg x) he.le)
  change (deviation epsilon x)^2 = variance x + epsilon at hs
  unfold variance at hs
  linarith only [hs]

theorem constant (epsilon t : ℝ) (gamma beta : Row) (i : Fin 4) :
    layerNorm epsilon (fun _ => t) gamma beta i = beta i := by
  simp [layerNorm, normalized, centered, mean]

theorem centering_identity (x y : Row) :
    squaredDistance (centered x) (centered y) =
      squaredDistance x y - 4 * (mean x - mean y)^2 := by
  simp [squaredDistance, sumSquares, centered, mean, Fin.sum_univ_succ]
  ring

theorem centering_distance (x y : Row) :
    squaredDistance (centered x) (centered y) ≤ squaredDistance x y := by
  rw [centering_identity]
  exact sub_le_self _ (by positivity)

theorem normalized_magnitude (epsilon : ℝ) (he : 0 < epsilon) (x : Row) (i : Fin 4) :
    |normalized epsilon x i| ≤ 2 := by
  have hr := deviation_pos epsilon he x
  have hc := coordinate_square_le (centered x) i
  rw [centered_sumSquares epsilon he x] at hc
  rw [normalized, abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  nlinarith only [hc, he]

theorem normalized_distance (epsilon : ℝ) (he : 0 < epsilon) (x y : Row) :
    deviation epsilon x * deviation epsilon y *
      squaredDistance (normalized epsilon x) (normalized epsilon y) ≤ squaredDistance x y := by
  exact (normalization_distance (centered x) (centered y)
    (deviation epsilon x) (deviation epsilon y) epsilon 4
    (deviation_pos epsilon he x) (deviation_pos epsilon he y) he.le (by norm_num)
    (centered_sumSquares epsilon he x) (centered_sumSquares epsilon he y)).trans
      (centering_distance x y)

theorem component_perturbation (epsilon delta lower : ℝ) (he : 0 < epsilon)
    (hd : 0 ≤ delta) (hl : 0 < lower) (x y : Row)
    (hx : lower ≤ deviation epsilon x) (hy : lower ≤ deviation epsilon y)
    (hxy : ∀ i, |x i - y i| ≤ delta) (i : Fin 4) :
    |normalized epsilon x i - normalized epsilon y i| ≤ 2 * delta / lower := by
  have hs (j : Fin 4) : (x j - y j)^2 ≤ delta^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x j - y j)) hd).mpr (hxy j)
  have hdistance : squaredDistance x y ≤ 4 * delta^2 := by
    calc
      _ ≤ ∑ _ : Fin 4, delta^2 := Finset.sum_le_sum (fun j _ => hs j)
      _ = _ := by simp
  have hr := deviation_pos epsilon he x
  have ht := deviation_pos epsilon he y
  have hp : lower^2 ≤ deviation epsilon x * deviation epsilon y := by
    simpa only [pow_two] using mul_le_mul hx hy hl.le hr.le
  have hc := coordinate_square_le
    (fun j => normalized epsilon x j - normalized epsilon y j) i
  have hc' := mul_le_mul_of_nonneg_left hc (mul_pos hr ht).le
  have hn := normalized_distance epsilon he x y
  have hsmall := mul_le_mul_of_nonneg_right hp
    (sq_nonneg (normalized epsilon x i - normalized epsilon y i))
  have hfinal : lower^2 * (normalized epsilon x i - normalized epsilon y i)^2 ≤
      4 * delta^2 := hsmall.trans (hc'.trans (hn.trans hdistance))
  apply (le_div_iff₀ hl).mpr
  apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hl.le) (by positivity)).mp
  nlinarith only [hfinal, sq_abs (normalized epsilon x i - normalized epsilon y i)]

theorem affine_perturbation (epsilon delta lower gain eta theta : ℝ)
    (he : 0 < epsilon) (hd : 0 ≤ delta) (hl : 0 < lower)
    (x y gamma gamma' beta beta' : Row)
    (hx : lower ≤ deviation epsilon x) (hy : lower ≤ deviation epsilon y)
    (hxy : ∀ i, |x i - y i| ≤ delta)
    (hg : ∀ i, |gamma' i| ≤ gain)
    (hgamma : ∀ i, |gamma' i - gamma i| ≤ eta)
    (hbeta : ∀ i, |beta' i - beta i| ≤ theta) (i : Fin 4) :
    |layerNorm epsilon y gamma' beta' i - layerNorm epsilon x gamma beta i| ≤
      gain * (2 * delta / lower) + 2 * eta + theta := by
  have hc := component_perturbation epsilon delta lower he hd hl y x hy hx
    (fun j => by simpa only [abs_sub_comm] using hxy j) i
  have hm := normalized_magnitude epsilon he x i
  have h1 := mul_le_mul hc (hg i) (abs_nonneg _) (by positivity : 0 ≤ 2 * delta / lower)
  have h2 := mul_le_mul hm (hgamma i) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hi : layerNorm epsilon y gamma' beta' i - layerNorm epsilon x gamma beta i =
      (normalized epsilon y i - normalized epsilon x i) * gamma' i +
        normalized epsilon x i * (gamma' i - gamma i) + (beta' i - beta i) := by
    unfold layerNorm
    ring
  rw [hi]
  calc
    _ ≤ |(normalized epsilon y i - normalized epsilon x i) * gamma' i| +
        |normalized epsilon x i * (gamma' i - gamma i)| + |beta' i - beta i| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ (2 * delta / lower) * gain + 2 * eta + theta := by
      simpa only [abs_mul] using add_le_add (add_le_add h1 h2) (hbeta i)
    _ = _ := by ring

theorem variance_floor_perturbation (epsilon delta floor : ℝ)
    (he : 0 < epsilon) (hd : 0 ≤ delta) (hf : 0 ≤ floor) (x y : Row)
    (hx : floor ≤ variance x) (hy : floor ≤ variance y)
    (hxy : ∀ i, |x i - y i| ≤ delta) (i : Fin 4) :
    |normalized epsilon x i - normalized epsilon y i| ≤
      2 * delta / Real.sqrt (floor + epsilon) := by
  exact component_perturbation epsilon delta (Real.sqrt (floor + epsilon)) he hd
    (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hf he)) x y
    (Real.sqrt_le_sqrt (add_le_add hx (le_refl epsilon)))
    (Real.sqrt_le_sqrt (add_le_add hy (le_refl epsilon))) hxy i

theorem implementation_perturbation (epsilon delta lower gain eta theta roundoff : ℝ)
    (he : 0 < epsilon) (hd : 0 ≤ delta) (hl : 0 < lower)
    (x y gamma gamma' beta beta' output : Row)
    (hx : lower ≤ deviation epsilon x) (hy : lower ≤ deviation epsilon y)
    (hxy : ∀ i, |x i - y i| ≤ delta)
    (hg : ∀ i, |gamma' i| ≤ gain)
    (hgamma : ∀ i, |gamma' i - gamma i| ≤ eta)
    (hbeta : ∀ i, |beta' i - beta i| ≤ theta)
    (hout : ∀ i, |output i - layerNorm epsilon y gamma' beta' i| ≤ roundoff) (i : Fin 4) :
    |output i - layerNorm epsilon x gamma beta i| ≤
      roundoff + gain * (2 * delta / lower) + 2 * eta + theta := by
  have hp := affine_perturbation epsilon delta lower gain eta theta he hd hl
    x y gamma gamma' beta beta' hx hy hxy hg hgamma hbeta i
  exact (abs_sub_le _ _ _).trans ((add_le_add (hout i) hp).trans_eq (by ring))

#print axioms constant
#print axioms normalized_magnitude
#print axioms normalized_distance
#print axioms component_perturbation
#print axioms affine_perturbation
#print axioms variance_floor_perturbation
#print axioms implementation_perturbation
end Project.LayerNorm.Real
