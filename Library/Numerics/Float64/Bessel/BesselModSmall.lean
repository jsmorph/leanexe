import Library.Numerics.Float64.Bessel.BesselSmallApprox

/-!
Lower bounds on the modulus of order 0 below 2, sharper than those of `BesselModulus`, for the
units of the theorems on `j0` and `y0`.  Kernel checks (`PolyBound.check`) bound the series `J₀`
and `C₀` of `Y₀` with 18 terms as polynomials in `ζ = x²/4` on pieces:

* `modulus0_half`: `√(J₀² + Y₀²) ≥ 1/2` on `[0, 2]`, from `J₀ ≥ 1/2` up to `3/2` and, on four
  pieces from `3/2` to 2, from lower bounds on `J₀`, on the series `C₀` of `Y₀`, and on
  `ln (x/2) + γ`;
* `Y0_log`: `Y₀(x) ≤ 0.597 ln x` for `0 < x ≤ 1/2`, so the modulus grows with `|ln x|`.

`BesselModSmall1` gives the bounds of order 1.
-/

namespace Library.Numerics.Float64.Bessel.BesselModSmall
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks Real BesselSmallApprox
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

theorem checks_J0 :
    check (subP (a0List 18) [75591 / 100000]) 0 (9 / 16) (611 / 2500) 5 = true ∧
      check (subP (a0List 18) [1489 / 3125]) (9 / 16) (169 / 256) (1783 / 50000) 2 = true ∧
      check (subP (a0List 18) [10127 / 25000]) (169 / 256) (49 / 64) (909 / 25000) 2 = true ∧
      check (subP (a0List 18) [33269 / 100000]) (49 / 64) (225 / 256) (733 / 20000) 2 = true ∧
      check (subP (a0List 18) [6503 / 25000]) (225 / 256) 1 (1827 / 50000) 3 = true ∧
      check (subP (a0List 18) [96923 / 100000]) 0 (1 / 16) (777 / 25000) 2 = true := by
  decide +kernel

theorem checks_C0 :
    check (subP (c0List 18) [12041 / 25000]) (9 / 16) (169 / 256) (2939 / 100000) 3 = true ∧
      check (subP (c0List 18) [53909 / 100000]) (169 / 256) (49 / 64) (717 / 25000) 3 = true ∧
      check (subP (c0List 18) [59459 / 100000]) (49 / 64) (225 / 256) (343 / 12500) 3 = true ∧
      check (subP (c0List 18) [64709 / 100000]) (225 / 256) 1 (321 / 12500) 3 = true ∧
      check (subP (c0List 18) [763 / 25000]) 0 (1 / 16) (3083 / 100000) 2 = true := by
  decide +kernel

/-- `c - r - 2^-99 ≤ f ≤ c + r + 2^-99` for a series `f` from a check of its partial sum. -/
theorem range_of_check (p : List ℚ) (c lo hi r : ℚ) (d : ℕ)
    (h : check (subP p [c]) lo hi r d = true) (ζ : ℝ) (h1 : (lo : ℝ) ≤ ζ) (h2 : ζ ≤ hi)
    (f : ℝ) (hf : |f - eval p ζ| ≤ 1 / 2 ^ 99) :
    (c : ℝ) - r - 1 / 2 ^ 99 ≤ f ∧ f ≤ (c : ℝ) + r + 1 / 2 ^ 99 := by
  have := check_sound _ lo hi r d h ζ h1 h2
  rw [eval_subP] at this
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at this
  rw [abs_le] at this hf
  constructor <;> linarith [this.1, this.2, hf.1, hf.2]

/-- The series against their partial sums, for `|x| ≤ 2`. -/
theorem series_close (x : ℝ) (hx : |x| ≤ 2) :
    |J0 x - eval (a0List 18) (x ^ 2 / 4)| ≤ 1 / 2 ^ 99 ∧
      |psum c0 (x ^ 2 / 4) - eval (c0List 18) (x ^ 2 / 4)| ≤ 1 / 2 ^ 99 := by
  obtain ⟨-, -, -, -, h18a, -, h18c, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts x hx
  exact ⟨rem_small (a := a0) (q := qa0) rfl h18a _ hz0 hz1
      (a0_remainder _ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num)),
    rem_small (a := c0) (q := qc0) rfl h18c _ hz0 hz1
      (c0_remainder _ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))⟩

theorem gamma_ge : (5772 / 10000 : ℝ) ≤ eulerMascheroniConstant := by
  have h1 := (gamma_sub_log_two).1
  have h2 := Real.log_two_gt_d9
  simp only [glo] at h1
  push_cast at h1
  norm_num at h1 h2 ⊢
  linarith

theorem two_div_pi_ge : (6366 / 10000 : ℝ) ≤ 2 / π := by
  rw [le_div_iff₀ Real.pi_pos]
  have := Real.pi_lt_d4
  nlinarith

/-- `Y₀ ≥ 0.6366 ((1 - 2/a + 0.5772) J + C)` on `[a, b]` with `J₀ ≥ J` and the series `≥ C`. -/
theorem Y0_lower (x a J C : ℝ) (ha : 3 / 2 ≤ a) (hx : a ≤ x) (hJ0 : 0 ≤ J) (hJ : J ≤ J0 x)
    (hC : C ≤ psum c0 (x ^ 2 / 4)) (hpos : 0 ≤ (1 - 2 / a + 5772 / 10000) * J + C) :
    6366 / 10000 * ((1 - 2 / a + 5772 / 10000) * J + C) ≤ Y0 x := by
  have hx0 : 0 < x := by linarith
  have hl : 1 - 2 / a ≤ log (x / 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < x / 2 by positivity)
    have : 1 - 2 / a ≤ 1 - (x / 2)⁻¹ := by
      rw [inv_div]
      have : 2 / x ≤ 2 / a := div_le_div_of_nonneg_left (by norm_num) (by linarith) hx
      linarith
    linarith
  have hg := gamma_ge
  have hp := two_div_pi_ge
  have hlg : 0 ≤ 1 - 2 / a + 5772 / 10000 := by
    have : 2 / a ≤ 4 / 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have h1 : (1 - 2 / a + 5772 / 10000) * J ≤ (log (x / 2) + eulerMascheroniConstant) * J0 x :=
    mul_le_mul (by linarith) hJ hJ0 (by linarith)
  have h2 : (1 - 2 / a + 5772 / 10000) * J + C ≤
      (log (x / 2) + eulerMascheroniConstant) * J0 x + psum c0 (x ^ 2 / 4) := by linarith
  rw [Y0]
  calc 6366 / 10000 * ((1 - 2 / a + 5772 / 10000) * J + C) ≤
        2 / π * ((1 - 2 / a + 5772 / 10000) * J + C) := mul_le_mul_of_nonneg_right hp hpos
    _ ≤ 2 / π * ((log (x / 2) + eulerMascheroniConstant) * J0 x + psum c0 (x ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem sq_bound {J Y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hJ : a ≤ J) (hY : b ≤ Y)
    (h : 1 / 4 ≤ a ^ 2 + b ^ 2) : 1 / 2 ≤ √(J ^ 2 + Y ^ 2) := by
  rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith

theorem zeta_mono {x a b : ℝ} (h0 : 0 ≤ a) (ha : a ≤ x) (hb : x ≤ b) :
    a ^ 2 / 4 ≤ x ^ 2 / 4 ∧ x ^ 2 / 4 ≤ b ^ 2 / 4 := by
  constructor <;> nlinarith

/-- `√(J₀² + Y₀²) ≥ 1/2` on `[0, 2]`. -/
theorem modulus0_half (x : ℝ) (h0 : 0 ≤ x) (h2 : x ≤ 2) : 1 / 2 ≤ √(J0 x ^ 2 + Y0 x ^ 2) := by
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := checks_J0
  obtain ⟨d1, d2, d3, d4, -⟩ := checks_C0
  obtain ⟨sJ, sC⟩ := series_close x (by rw [abs_of_nonneg h0]; exact h2)
  have e : (1 : ℝ) / 2 ^ 99 ≤ 1 / 10 ^ 20 := by norm_num
  rcases le_total x (3 / 2) with h | h
  · obtain ⟨z1, z2⟩ := zeta_mono (le_refl 0) h0 h
    have r := range_of_check _ _ _ _ _ _ c0 _ (by push_cast; linarith) (by push_cast; linarith) _ sJ
    push_cast at r
    have hJ : 1 / 2 ≤ J0 x := by linarith [r.1]
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (Y0 x), hJ]
  rcases le_total x (13 / 8) with h' | h'
  · obtain ⟨z1, z2⟩ := zeta_mono (by norm_num) h h'
    have rj := range_of_check _ _ _ _ _ _ c1 _ (by push_cast; linarith) (by push_cast; linarith) _ sJ
    have rc := range_of_check _ _ _ _ _ _ d1 _ (by push_cast; linarith) (by push_cast; linarith) _ sC
    push_cast at rj rc
    have hY := Y0_lower x (3 / 2) (44081 / 100000) (45224 / 100000) le_rfl h (by norm_num)
      (by linarith) (by linarith) (by norm_num)
    exact sq_bound (a := 44081 / 100000) (by norm_num) (by norm_num) (by linarith) hY (by norm_num)
  rcases le_total x (7 / 4) with h'' | h''
  · obtain ⟨z1, z2⟩ := zeta_mono (by norm_num) h' h''
    have rj := range_of_check _ _ _ _ _ _ c2 _ (by push_cast; linarith) (by push_cast; linarith) _ sJ
    have rc := range_of_check _ _ _ _ _ _ d2 _ (by push_cast; linarith) (by push_cast; linarith) _ sC
    push_cast at rj rc
    have hY := Y0_lower x (13 / 8) (36871 / 100000) (51040 / 100000) (by norm_num) h' (by norm_num)
      (by linarith) (by linarith) (by norm_num)
    exact sq_bound (a := 36871 / 100000) (by norm_num) (by norm_num) (by linarith) hY (by norm_num)
  rcases le_total x (15 / 8) with h3 | h3
  · obtain ⟨z1, z2⟩ := zeta_mono (by norm_num) h'' h3
    have rj := range_of_check _ _ _ _ _ _ c3 _ (by push_cast; linarith) (by push_cast; linarith) _ sJ
    have rc := range_of_check _ _ _ _ _ _ d3 _ (by push_cast; linarith) (by push_cast; linarith) _ sC
    push_cast at rj rc
    have hY := Y0_lower x (7 / 4) (29603 / 100000) (56714 / 100000) (by norm_num) h'' (by norm_num)
      (by linarith) (by linarith) (by norm_num)
    exact sq_bound (a := 29603 / 100000) (by norm_num) (by norm_num) (by linarith) hY (by norm_num)
  · obtain ⟨z1, z2⟩ := zeta_mono (by norm_num) h3 h2
    have rj := range_of_check _ _ _ _ _ _ c4 _ (by push_cast; linarith) (by push_cast; linarith) _ sJ
    have rc := range_of_check _ _ _ _ _ _ d4 _ (by push_cast; linarith) (by push_cast; linarith) _ sC
    push_cast at rj rc
    have hY := Y0_lower x (15 / 8) (22357 / 100000) (62140 / 100000) (by norm_num) h3 (by norm_num)
      (by linarith) (by linarith) (by norm_num)
    exact sq_bound (a := 22357 / 100000) (by norm_num) (by norm_num) (by linarith) hY (by norm_num)

/-- `Y₀ x ≤ 0.597 ln x` for `0 < x ≤ 1/2`. -/
theorem Y0_log (x : ℝ) (h0 : 0 < x) (h2 : x ≤ 1 / 2) : Y0 x ≤ 597 / 1000 * log x := by
  obtain ⟨-, -, -, -, -, c5⟩ := checks_J0
  obtain ⟨-, -, -, -, d5⟩ := checks_C0
  obtain ⟨sJ, sC⟩ := series_close x (by rw [abs_of_pos h0]; linarith)
  have e : (1 : ℝ) / 2 ^ 99 ≤ 1 / 10 ^ 20 := by norm_num
  obtain ⟨z1, z2⟩ := zeta_mono (le_refl 0) h0.le h2
  have rj := range_of_check _ _ _ _ _ _ c5 _ (by push_cast; linarith) (by push_cast; linarith) _ sJ
  have rc := range_of_check _ _ _ _ _ _ d5 _ (by push_cast; linarith) (by push_cast; linarith) _ sC
  push_cast at rj rc
  have hlog : log x ≤ -(6931 / 10000) := by
    have h := Real.log_le_log h0 h2
    rw [one_div, Real.log_inv] at h
    have := Real.log_two_gt_d9
    linarith
  have hg := gamma_sub_log_two.2
  simp only [ghi] at hg
  push_cast at hg
  have hb : log (x / 2) + eulerMascheroniConstant ≤ log x - 1159 / 10000 := by
    rw [Real.log_div h0.ne' two_ne_zero]
    norm_num at hg
    linarith
  have hneg : log (x / 2) + eulerMascheroniConstant < 0 := by linarith
  have hJ : 938 / 1000 ≤ J0 x := by linarith [rj.1]
  have h1 : (log (x / 2) + eulerMascheroniConstant) * J0 x ≤
      (log (x / 2) + eulerMascheroniConstant) * (938 / 1000) :=
    mul_le_mul_of_nonpos_left hJ hneg.le
  have hC : psum c0 (x ^ 2 / 4) ≤ 625 / 10000 := by linarith [rc.2]
  have hB : (log (x / 2) + eulerMascheroniConstant) * J0 x + psum c0 (x ^ 2 / 4) ≤
      938 / 1000 * log x - 46 / 1000 := by nlinarith
  have hp := two_div_pi_ge
  have hBn : 938 / 1000 * log x - 46 / 1000 < 0 := by linarith
  rw [Y0]
  calc 2 / π * ((log (x / 2) + eulerMascheroniConstant) * J0 x + psum c0 (x ^ 2 / 4)) ≤
        2 / π * (938 / 1000 * log x - 46 / 1000) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ 6366 / 10000 * (938 / 1000 * log x - 46 / 1000) :=
        mul_le_mul_of_nonpos_right hp hBn.le
    _ ≤ 597 / 1000 * log x := by nlinarith

#print axioms checks_J0
#print axioms checks_C0
#print axioms modulus0_half
#print axioms Y0_log

end Library.Numerics.Float64.Bessel.BesselModSmall
