import Library.Numerics.Float64.Bessel.BesselModSmall

/-!
Lower bounds on `√(J₁² + Y₁²)` below 2, for the units of the theorems on `j1` and `y1`.  Kernel
checks bound the series `A₁ = 2 J₁ / x` and `C₁` of `Y₁` with 18 terms in `ζ = x²/4`:

* `modulus1_small`: `√(J₁² + Y₁²) ≥ 2/(π x)` for `0 < x ≤ 1`, since `Y₁ ≤ -2/(π x)` there
  (`Y1_small`): `ln (x/2) + γ < 0`, `A₁ ≥ 0.88`, and `C₁ ≥ 0.70`;
* `J1lo_le`: `J₁ ≥ J1lo x` on `[1, 2]`, with `J1lo` from `0.4249` on `[1, 9/8]` to `0.5611` on
  `[15/8, 31/16]`, from `J₁ ≥ (a/2) min A₁` on a piece `[a, b]`;
* `modulus1_lower`: `√(J₁² + Y₁²) ≥ 0.42` for `0 < x ≤ 2`.
-/

namespace Library.Numerics.Float64.Bessel.BesselModSmall1
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks Real BesselSmallApprox BesselModSmall
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

theorem checks_A1 :
    check (subP (a1List 18) [52405 / 55747]) 0 (1 / 4) (559 / 9309) 3 = true ∧
      check (subP (a1List 18) [23178 / 26795]) (1 / 4) (81 / 256) (509 / 33511) 1 = true ∧
      check (subP (a1List 18) [25193 / 30227]) (81 / 256) (25 / 64) (1296 / 78247) 1 = true ∧
      check (subP (a1List 18) [64006 / 82011]) (25 / 64) (9 / 16) (2943 / 80320) 2 = true ∧
      check (subP (a1List 18) [70216 / 99813]) (9 / 16) (49 / 64) (3938 / 97139) 2 = true ∧
      check (subP (a1List 18) [46073 / 71796]) (49 / 64) (225 / 256) (33 / 1541) 2 = true ∧
      check (subP (a1List 18) [17848 / 29281]) (225 / 256) (961 / 1024) (39 / 3557) 1 = true ∧
      check (subP (a1List 18) [3431 / 5838]) (961 / 1024) 1 (103 / 9299) 1 = true := by
  decide +kernel

theorem checks_C1 : check (subP (c1List 18) [17785 / 20869]) 0 (1 / 4) (2503 / 16926) 4 = true := by
  decide +kernel

/-- The series of `J₁` and `Y₁` against their partial sums, for `|x| ≤ 2`. -/
theorem series_close1 (x : ℝ) (hx : |x| ≤ 2) :
    |psum a1 (x ^ 2 / 4) - eval (a1List 18) (x ^ 2 / 4)| ≤ 1 / 2 ^ 99 ∧
      |psum c1 (x ^ 2 / 4) - eval (c1List 18) (x ^ 2 / 4)| ≤ 1 / 2 ^ 99 := by
  obtain ⟨-, -, -, -, -, h18a, -, h18c, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts x hx
  exact ⟨rem_small (a := a1) (q := qa1) rfl h18a _ hz0 hz1
      (a1_remainder _ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num)),
    rem_small (a := c1) (q := qc1) rfl h18c _ hz0 hz1
      (c1_remainder _ (by rw [abs_of_nonneg hz0]; exact hz1) 18 (by norm_num))⟩

/-- `J₁ x ≥ (a/2) (c - r - 2^-99)` on `[a, b]` from a check of `A₁` on `[a²/4, b²/4]`. -/
theorem J1_piece (x a b : ℝ) (c lo hi r : ℚ) (d : ℕ)
    (h : check (subP (a1List 18) [c]) lo hi r d = true) (ha0 : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hb2 : b ≤ 2) (hlo : (lo : ℝ) ≤ a ^ 2 / 4) (hhi : b ^ 2 / 4 ≤ (hi : ℝ)) (L : ℝ)
    (hL : L ≤ a / 2 * ((c : ℝ) - r - 1 / 2 ^ 99)) (hpos : 0 ≤ (c : ℝ) - r - 1 / 2 ^ 99) :
    L ≤ J1 x := by
  have hs := (series_close1 x (by rw [abs_of_nonneg (by linarith)]; linarith)).1
  obtain ⟨z1, z2⟩ := zeta_mono ha0 hax hxb
  have rr := range_of_check _ _ _ _ _ _ h _ (by linarith) (by linarith) _ hs
  have hJ : J1 x = x / 2 * psum a1 (x ^ 2 / 4) := rfl
  rw [hJ]
  exact hL.trans (mul_le_mul (by linarith) rr.1 hpos (by linarith))

/-- The lower bound of `J₁` on `[1, 2]`, by piece. -/
noncomputable def J1lo (x : ℝ) : ℝ :=
  if x ≤ 9 / 8 then 4249 / 10000 else if x ≤ 5 / 4 then 919 / 2000
  else if x ≤ 3 / 2 then 581 / 1250 else if x ≤ 7 / 4 then 1243 / 2500
  else if x ≤ 15 / 8 then 5427 / 10000 else if x ≤ 31 / 16 then 5611 / 10000 else 2793 / 5000

theorem J1lo_ge (x : ℝ) : 4249 / 10000 ≤ J1lo x := by
  unfold J1lo
  split_ifs <;> norm_num

theorem J1lo_le (x : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ 2) : J1lo x ≤ J1 x := by
  obtain ⟨-, k1, k2, k3, k4, k5, k6, k7⟩ := checks_A1
  unfold J1lo
  split_ifs with c1 c2 c3 c4 c5 c6
  · exact J1_piece x 1 (9 / 8) _ _ _ _ _ k1 (by norm_num) h1 c1 (by norm_num) (by norm_num)
      (by norm_num) _ (by norm_num) (by norm_num)
  · exact J1_piece x (9 / 8) (5 / 4) _ _ _ _ _ k2 (by norm_num) (not_le.mp c1).le c2 (by norm_num)
      (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)
  · exact J1_piece x (5 / 4) (3 / 2) _ _ _ _ _ k3 (by norm_num) (not_le.mp c2).le c3 (by norm_num)
      (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)
  · exact J1_piece x (3 / 2) (7 / 4) _ _ _ _ _ k4 (by norm_num) (not_le.mp c3).le c4 (by norm_num)
      (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)
  · exact J1_piece x (7 / 4) (15 / 8) _ _ _ _ _ k5 (by norm_num) (not_le.mp c4).le c5 (by norm_num)
      (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)
  · exact J1_piece x (15 / 8) (31 / 16) _ _ _ _ _ k6 (by norm_num) (not_le.mp c5).le c6
      (by norm_num) (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)
  · exact J1_piece x (31 / 16) 2 _ _ _ _ _ k7 (by norm_num) (not_le.mp c6).le h2 (by norm_num)
      (by norm_num) (by norm_num) _ (by norm_num) (by norm_num)

/-- `Y₁ x ≤ -2/(π x)` for `0 < x ≤ 1`. -/
theorem Y1_small (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) : Y1 x ≤ -(2 / (π * x)) := by
  obtain ⟨k0, -⟩ := checks_A1
  have kc := checks_C1
  obtain ⟨sa, sc⟩ := series_close1 x (by rw [abs_of_pos h0]; linarith)
  obtain ⟨z1, z2⟩ := zeta_mono (le_refl 0) h0.le h1
  have ra := range_of_check _ _ _ _ _ _ k0 _ (by push_cast; linarith) (by push_cast; linarith) _ sa
  have rc := range_of_check _ _ _ _ _ _ kc _ (by push_cast; linarith) (by push_cast; linarith) _ sc
  push_cast at ra rc
  have e : (1 : ℝ) / 2 ^ 99 ≤ 1 / 10 ^ 20 := by norm_num
  have hA : 0 ≤ psum a1 (x ^ 2 / 4) := by linarith [ra.1]
  have hC : 0 ≤ psum c1 (x ^ 2 / 4) := by linarith [rc.1]
  have hJ : 0 ≤ J1 x := mul_nonneg (by positivity) hA
  have hlog : log (x / 2) ≤ -log 2 := by
    have := Real.log_le_log (by positivity) (show x / 2 ≤ 1 / 2 by linarith)
    rwa [one_div, Real.log_inv] at this
  have hg := gamma_sub_log_two.2
  simp only [ghi] at hg
  push_cast at hg
  have hneg : log (x / 2) + eulerMascheroniConstant ≤ 0 := by norm_num at hg; linarith
  have hp : 0 < 2 / π := by positivity
  have t1 : 2 / π * (log (x / 2) + eulerMascheroniConstant) * J1 x ≤ 0 := by
    nlinarith [mul_nonneg hp.le hJ]
  have t3 : 0 ≤ x / (2 * π) * psum c1 (x ^ 2 / 4) := mul_nonneg (by positivity) hC
  unfold Y1
  linarith

theorem mod_ge_J {J Y a : ℝ} (ha : 0 ≤ a) (h : a ≤ J) : a ≤ √(J ^ 2 + Y ^ 2) := by
  rw [show a = √(a ^ 2) by rw [Real.sqrt_sq ha]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Y])

/-- `√(J₁² + Y₁²) ≥ 2/(π x)` for `0 < x ≤ 1`. -/
theorem modulus1_small (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    2 / (π * x) ≤ √(J1 x ^ 2 + Y1 x ^ 2) := by
  have hY := Y1_small x h0 h1
  have hp : 0 ≤ 2 / (π * x) := by positivity
  rw [show 2 / (π * x) = √((2 / (π * x)) ^ 2) by rw [Real.sqrt_sq hp]]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (J1 x)]

/-- `√(J₁² + Y₁²) ≥ 0.42` for `0 < x ≤ 2`. -/
theorem modulus1_lower (x : ℝ) (h0 : 0 < x) (h2 : x ≤ 2) :
    42 / 100 ≤ √(J1 x ^ 2 + Y1 x ^ 2) := by
  rcases le_total x 1 with h1 | h1
  · have hm := modulus1_small x h0 h1
    have hp := two_div_pi_ge
    have : 2 / π ≤ 2 / (π * x) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [Real.pi_pos])
    linarith
  · have := J1lo_le x h1 h2
    have := J1lo_ge x
    exact mod_ge_J (by norm_num) (by linarith)

#print axioms checks_A1
#print axioms checks_C1
#print axioms J1lo_le
#print axioms Y1_small
#print axioms modulus1_small
#print axioms modulus1_lower

end Library.Numerics.Float64.Bessel.BesselModSmall1
