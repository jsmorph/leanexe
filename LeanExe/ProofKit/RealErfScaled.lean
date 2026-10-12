import LeanExe.ProofKit.RealErf

/-!
`erfcxN x = erfcx x / (2/√π) = (√π/2) exp (x²) erfc x`, which satisfies `erfcxN' = 2 x erfcxN - 1`
without the constant `2/√π`, so that polynomial models checked against the equation carry no
error from the enclosure of `π`.  The comparison lemma `ode_backward` holds for any function with
derivative `2 x G - k`, and the asymptotic bounds of `erfcx` become rational bounds on `erfcxN`.
-/

namespace LeanExe.ProofKit.RealErfScaled
open Real Set RealErf

/-- `erfcx x / (2/√π)`. -/
noncomputable def erfcxN (x : ℝ) : ℝ := erfcx x / scale

theorem hasDerivAt_erfcxN (x : ℝ) : HasDerivAt erfcxN (2 * x * erfcxN x - 1) x := by
  have h := (hasDerivAt_erfcx x).div_const scale
  have hf : erfcxN = fun x => erfcx x / scale := rfl
  rw [hf]
  refine h.congr_deriv ?_
  have hs : scale ≠ 0 := scale_pos.ne'
  field_simp

theorem erfcxN_pos (x : ℝ) : 0 < erfcxN x := div_pos (erfcx_pos x) scale_pos

theorem erfcx_eq (x : ℝ) : erfcx x = scale * erfcxN x := by
  have hs : scale ≠ 0 := scale_pos.ne'
  rw [erfcxN]
  field_simp

/-- A function `p` with `|p' - 2 x p + k| ≤ η` on `[a, b]`, `0 ≤ a`, stays within
`σ + η (b - x)` of any `G` with `G' = 2 x G - k` that it approximates within `σ` at `b`. -/
theorem ode_backward (G : ℝ → ℝ) (k : ℝ) (hG : ∀ x, HasDerivAt G (2 * x * G x - k) x)
    (p p' : ℝ → ℝ) {a b σ η : ℝ} (ha : 0 ≤ a)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hδ : ∀ x ∈ Icc a b, |p' x - 2 * x * p x + k| ≤ η)
    (hb : |G b - p b| ≤ σ) {x : ℝ} (hx : x ∈ Icc a b) :
    |G x - p x| ≤ σ + η * (b - x) := by
  set w := fun u => exp (-u ^ 2) * (G u - p u) with hw
  have hwd : ∀ u ∈ Icc x b, HasDerivAt w (-(exp (-u ^ 2) * (p' u - 2 * u * p u + k))) u := by
    intro u hu
    have hu' : u ∈ Icc a b := ⟨hx.1.trans hu.1, hu.2⟩
    have h := (hasDerivAt_gauss u).mul ((hG u).sub (hp u hu'))
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hbound : ∀ u ∈ Ico x b, ‖-(exp (-u ^ 2) * (p' u - 2 * u * p u + k))‖ ≤
      exp (-x ^ 2) * η := by
    intro u hu
    have hu' : u ∈ Icc a b := ⟨hx.1.trans hu.1, hu.2.le⟩
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hle : exp (-u ^ 2) ≤ exp (-x ^ 2) := by
      apply exp_le_exp.mpr
      nlinarith [hu.1]
    exact mul_le_mul hle (hδ u hu') (abs_nonneg _) (exp_pos _).le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (hwd u hu).hasDerivWithinAt) hbound b ⟨hx.2, le_rfl⟩
  rw [Real.norm_eq_abs] at hmv
  have hwx : G x - p x = exp (x ^ 2) * w x := by
    simp only [hw]
    rw [← mul_assoc, ← exp_add]
    simp
  have hwb : |w b| ≤ exp (-b ^ 2) * σ := by
    simp only [hw]
    rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left hb (exp_pos _).le
  have hwx' : |w x| ≤ exp (-b ^ 2) * σ + exp (-x ^ 2) * η * (b - x) := by
    have h := abs_sub_abs_le_abs_sub (w x) (w b)
    rw [abs_sub_comm] at hmv
    linarith
  have hη : 0 ≤ η := (abs_nonneg _).trans (hδ x hx)
  have hσ : 0 ≤ σ := (abs_nonneg _).trans hb
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hxb : exp (x ^ 2) * exp (-b ^ 2) ≤ 1 := by
    rw [← exp_add]
    apply exp_le_one_iff.mpr
    nlinarith [hx.2]
  have hxx : exp (x ^ 2) * exp (-x ^ 2) = 1 := by rw [← exp_add]; simp
  rw [hwx, abs_mul, abs_of_pos (exp_pos _)]
  calc exp (x ^ 2) * |w x| ≤ exp (x ^ 2) * (exp (-b ^ 2) * σ + exp (-x ^ 2) * η * (b - x)) :=
        mul_le_mul_of_nonneg_left hwx' (exp_pos _).le
    _ = (exp (x ^ 2) * exp (-b ^ 2)) * σ + (exp (x ^ 2) * exp (-x ^ 2)) * η * (b - x) := by
        ring
    _ ≤ 1 * σ + 1 * η * (b - x) := by
        rw [hxx]
        have hbx : 0 ≤ b - x := by linarith [hx.2]
        nlinarith
    _ = σ + η * (b - x) := by ring

theorem erfcxN_backward (p p' : ℝ → ℝ) {a b σ η : ℝ} (ha : 0 ≤ a)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hδ : ∀ x ∈ Icc a b, |p' x - 2 * x * p x + 1| ≤ η)
    (hb : |erfcxN b - p b| ≤ σ) {x : ℝ} (hx : x ∈ Icc a b) :
    |erfcxN x - p x| ≤ σ + η * (b - x) :=
  ode_backward erfcxN 1 hasDerivAt_erfcxN p p' ha hp hδ hb hx

/-- The asymptotic bounds of `erfcxN`: for `x > 0`, `asymSum N x / 2` is at most `erfcxN x` for
even `N` and at least `erfcxN x` for odd `N`. -/
theorem erfcxN_asym (N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1) ^ N * (erfcxN x - asymSum N x / 2) := by
  have h := erfcx_asym N hx
  rw [erfcx_eq] at h
  have hs := scale_pos
  have he : (-1) ^ N * (scale * erfcxN x - scale / 2 * asymSum N x) =
      scale * ((-1) ^ N * (erfcxN x - asymSum N x / 2)) := by ring
  rw [he] at h
  exact (mul_nonneg_iff_of_pos_left hs).mp h

#print axioms hasDerivAt_erfcxN
#print axioms ode_backward
#print axioms erfcxN_backward
#print axioms erfcxN_asym

end LeanExe.ProofKit.RealErfScaled
