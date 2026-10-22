import Library.Numerics.Float64.Tgamma.TgammaAccFinish
import Library.Numerics.Float64.Tgamma.TgammaAccPre

/-!
The cases `x ≥ j` of the accurate path of `Tgamma` from `1/4`.  For `x ≥ j + 1` the loop forms
`D = (x - 1) (x - 2) ⋯ (x - M - 1)` with `M + 1 = ⌊x⌋ - j ≤ 31` factors, each at least 4, so
`Γ x = Γ (x - M - 1) D` and the code multiplies the polynomial by `wh + wl` (`down_case`).  For
`j ≤ x < j + 1` the code keeps the polynomial (`zero_case`).  The scale `eoff` of the range stays,
and `Γ x ≤ Γ (t0⁻) ≤ 2 ^ 1024 (1 - 2 ^ -50)` keeps the result finite.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccDownCase
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAccUp TgammaAccDown
  TgammaAccFin TgammaAccCrr TgammaAccBounds TgammaAccFinish

set_option exponentiation.threshold 4096

/-- The bounds on the polynomial `p1 + p2` of a range that the steps after it need. -/
theorem poly_facts (p1 p2 : Float) (A : ℝ) (hA1 : 1 / 17 ≤ A)
    (hpA : |value p1.toBits + value p2.toBits - A| ≤ 1 / 2 ^ 63)
    (hp1b : |value p1.toBits| ≤ 120) (hp2b : |value p2.toBits| ≤ 1 / 2 ^ 37) :
    A ≤ 121 ∧ 1 / 32 ≤ |value p1.toBits| ∧
      |value p2.toBits| ≤ |value p1.toBits| / 2 ^ 30 ∧
      |value p1.toBits + value p2.toBits - A| ≤ 17 / 2 ^ 63 * |A| := by
  have hPA2 := abs_le.mp hpA
  have hPab := abs_add_le (value p1.toBits) (value p2.toBits)
  have h2 := le_abs_self (value p1.toBits + value p2.toBits)
  have hA121 : A ≤ 121 := by
    linarith [(by norm_num : (120 : ℝ) + 1 / 2 ^ 37 + 1 / 2 ^ 63 ≤ 121)]
  have hp1lo : 1 / 32 ≤ |value p1.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub (value p1.toBits + value p2.toBits) (value p2.toBits)
    rw [add_sub_cancel_right] at h1
    linarith [(by norm_num : (1 : ℝ) / 32 ≤ 1 / 17 - 1 / 2 ^ 63 - 1 / 2 ^ 37)]
  refine ⟨hA121, hp1lo, ?_, ?_⟩
  · have : (1 : ℝ) / 32 / 2 ^ 30 ≤ |value p1.toBits| / 2 ^ 30 :=
      div_le_div_of_nonneg_right hp1lo (by positivity)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 37 ≤ 1 / 32 / 2 ^ 30)]
  · rw [abs_of_pos (by linarith : (0 : ℝ) < A)]
    linarith

/-- `Γ` below `t0` from 2 on is at most `2 ^ 1024 (1 - 2 ^ -50)`. -/
theorem gamma_le_max (hT : TgammaLarge.GammaBelowT0) (x : Float) (hx : Finite x.toBits)
    (h2 : 2 ≤ value x.toBits) (ht : value x.toBits < (GammaThresholds.t0 : ℝ)) :
    |Real.Gamma (value x.toBits)| ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50) := by
  have hq := TgammaLarge.below_t0 x hx (by linarith) ht
  rw [abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  exact (Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr h2)
    (Set.mem_Ici.mpr (by linarith)) hq).trans hT

/-- **The path for `x ≥ j + 1`.** -/
theorem down_case (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hT : TgammaLarge.GammaBelowT0) (x : Float)
    (hx : Finite x.toBits) (ht : value x.toBits < (GammaThresholds.t0 : ℝ)) (M : ℕ)
    (hM : M + 1 ≤ 31) (hy4 : 4 ≤ value x.toBits - (M + 1 : ℕ)) (hv8 : value x.toBits ≤ 2 ^ 8)
    (eoff : ℕ) (he : eoff ≤ 1500) (A : ℝ) (hA1 : 1 / 17 ≤ A)
    (hΓ : |Real.Gamma (value x.toBits - (M + 1 : ℕ)) - 2 ^ eoff * A| ≤
      1 / 2 ^ 62 * Real.Gamma (value x.toBits - (M + 1 : ℕ)))
    (p1 p2 : Float) (hp1 : Finite p1.toBits) (hp2 : Finite p2.toBits)
    (hpA : |value p1.toBits + value p2.toBits - A| ≤ 1 / 2 ^ 63)
    (hp1b : |value p1.toBits| ≤ 120) (hp2b : |value p2.toBits| ≤ 1 / 2 ^ 37)
    (wh wl : Float) (hwhf : Finite wh.toBits) (hwlf : Finite wl.toBits)
    (hWe : |value wh.toBits + value wl.toBits - D (value x.toBits) M| ≤
      M / 2 ^ 95 * |D (value x.toBits) M|)
    (hwlb : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 50) (hwhb : |value wh.toBits| ≤ 2 ^ 518)
    (jm : Float) (hjmf : Finite jm.toBits) (hjm : value jm.toBits = -((M : ℝ) + 1)) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (Float.ofBits (finRes (mulDD3 p1 p2 wh wl).1
        (adjLow (mulDD3 p1 p2 wh wl).1 (mulDD3 p1 p2 wh wl).2 jm) (UInt64.ofNat eoff))).toBits := by
  set v := value x.toBits with hvdef
  set Dv := D v M with hDvdef
  have hP : (0 : ℝ) < 2 ^ eoff := by positivity
  obtain ⟨hA121, hp1lo, hp2r, hPA⟩ := poly_facts p1 p2 A hA1 hpA hp1b hp2b
  have hMr : (M : ℝ) + 1 ≤ 31 := by exact_mod_cast hM
  -- the product
  have hD4 : 4 ≤ Dv := by
    have h1 : ∏ _i ∈ Finset.range (M + 1), (4 : ℝ) ≤ Dv := by
      rw [hDvdef, D]
      apply Finset.prod_le_prod (fun _ _ => by norm_num)
      intro i hi
      have hi' : ((i + 1 : ℕ) : ℝ) ≤ (M + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      linarith
    rw [Finset.prod_const, Finset.card_range] at h1
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (M + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ Dv := h1
  have hD248 : Dv ≤ 2 ^ 248 := by
    have h1 : Dv ≤ ∏ _i ∈ Finset.range (M + 1), (2 : ℝ) ^ 8 := by
      rw [hDvdef, D]
      apply Finset.prod_le_prod
      · intro i hi
        have hi' : ((i + 1 : ℕ) : ℝ) ≤ (M + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        linarith
      · intro i _
        have : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    rw [Finset.prod_const, Finset.card_range, ← pow_mul] at h1
    exact h1.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hDabs : |Dv| = Dv := abs_of_pos (by linarith)
  have hβ : (M : ℝ) / 2 ^ 95 ≤ 30 / 2 ^ 95 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hWe' : |value wh.toBits + value wl.toBits - Dv| ≤ 30 / 2 ^ 95 * |Dv| :=
    hWe.trans (mul_le_mul_of_nonneg_right hβ (abs_nonneg _))
  set Wd := value wh.toBits + value wl.toBits with hWddef
  have hwh1 : 1 ≤ |value wh.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub Dv Wd
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le (value wh.toBits) (value wl.toBits)
    have h3 : |value wh.toBits| / 2 ^ 50 ≤ |value wh.toBits| :=
      div_le_self (abs_nonneg _) (by norm_num)
    rw [hDabs] at h1 hWe'
    linarith
  have hwh2 : |value wh.toBits| ≤ 2 ^ 519 := by
    linarith [(by norm_num : (2 : ℝ) ^ 518 ≤ 2 ^ 519)]
  -- the product of the polynomial and `wh + wl`
  obtain ⟨hf1f, hf2f, hfq, hf2r⟩ := TgammaAccComb.mul_step hF p1 p2 wh wl hp1 hp2 hwhf hwlf hp2r
    hp1lo (by linarith [(by norm_num : (120 : ℝ) ≤ 2 ^ 8)]) hwlb hwh1 hwh2
  set f := mulDD3 p1 p2 wh wl with hfdef
  have hf2r30 : |value f.2.toBits| ≤ |value f.1.toBits| / 2 ^ 30 :=
    hf2r.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num))
  set P := value p1.toBits + value p2.toBits with hPdef
  have hQ := rel_mul P A Wd Dv (17 / 2 ^ 63) (30 / 2 ^ 95) (by norm_num) hPA hWe'
  have hε : (17 / 2 ^ 63 + 30 / 2 ^ 95 + 17 / 2 ^ 63 * (30 / 2 ^ 95)) ≤ (18 : ℝ) / 2 ^ 63 := by
    norm_num
  have hε0 : (0 : ℝ) ≤ 17 / 2 ^ 63 + 30 / 2 ^ 95 + 17 / 2 ^ 63 * (30 / 2 ^ 95) := by norm_num
  have hQ01 : 1 / 2 ^ 800 ≤ |A * Dv| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < A), hDabs]
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 800 ≤ 1 / 17 * 4)]
  have hQ02 : |A * Dv| ≤ 2 ^ 800 := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < A), hDabs]
    have := mul_le_mul hA121 hD248 (by linarith) (by norm_num)
    linarith [(by norm_num : (121 : ℝ) * 2 ^ 248 ≤ 2 ^ 800)]
  -- `Γ`
  set y := v - ((M + 1 : ℕ) : ℝ) with hydef
  have hNPy : GammaBasic.NotPole y := fun m hm => by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hprod := GammaBasic.gamma_add_nat hNPy (M + 1)
  have hyv : y + ((M + 1 : ℕ) : ℝ) = v := by rw [hydef]; ring
  rw [hyv] at hprod
  have hrefl := Finset.prod_range_reflect (fun j : ℕ => y + (j : ℝ)) (M + 1)
  have hDp : ∏ j ∈ Finset.range (M + 1), (y + (j : ℝ)) = Dv := by
    rw [← hrefl, hDvdef, D]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc : ((M + 1 - 1 - i : ℕ) : ℝ) = M - i := by
      rw [show M + 1 - 1 - i = M - i by omega, Nat.cast_sub hi']
    rw [hc, hydef]
    push_cast
    ring
  rw [hDp] at hprod
  set Γy := Real.Gamma y with hΓydef
  have hΓy : 0 < Γy := Real.Gamma_pos_of_pos (by linarith)
  have hsc := scale_rel A Γy (2 ^ eoff) Dv hP hΓy hΓ
  rw [← hprod] at hsc
  have hjmb : |value jm.toBits| ≤ 200 := by
    rw [hjm, abs_neg, abs_of_pos (by positivity)]
    linarith
  exact finish_pos f.1 f.2 jm eoff (Real.Gamma v) (P * Wd) (A * Dv) _ hf1f hf2f hjmf hjmb
    hf2r30 hfq hε0 hε hQ hsc hQ01 hQ02 he
    (gamma_le_max hT x hx (by linarith [(Nat.cast_nonneg (M + 1) : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ))])
      ht)

/-- **The path for `j ≤ x < j + 1`.** -/
theorem zero_case (hT : TgammaLarge.GammaBelowT0) (x : Float) (hx : Finite x.toBits)
    (ht : value x.toBits < (GammaThresholds.t0 : ℝ)) (hy4 : 4 ≤ value x.toBits)
    (eoff : ℕ) (he : eoff ≤ 1500) (A : ℝ) (hA1 : 1 / 17 ≤ A)
    (hΓ : |Real.Gamma (value x.toBits) - 2 ^ eoff * A| ≤ 1 / 2 ^ 62 * Real.Gamma (value x.toBits))
    (p1 p2 : Float) (hp1 : Finite p1.toBits) (hp2 : Finite p2.toBits)
    (hpA : |value p1.toBits + value p2.toBits - A| ≤ 1 / 2 ^ 63)
    (hp1b : |value p1.toBits| ≤ 120) (hp2b : |value p2.toBits| ≤ 1 / 2 ^ 37)
    (jm : Float) (hjmf : Finite jm.toBits) (hjm : value jm.toBits = 0) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (Float.ofBits (finRes p1 (adjLow p1 p2 jm) (UInt64.ofNat eoff))).toBits := by
  set v := value x.toBits with hvdef
  have hP : (0 : ℝ) < 2 ^ eoff := by positivity
  obtain ⟨hA121, hp1lo, hp2r, hPA⟩ := poly_facts p1 p2 A hA1 hpA hp1b hp2b
  have hΓy : 0 < Real.Gamma v := Real.Gamma_pos_of_pos (by linarith)
  have hsc := scale_rel A (Real.Gamma v) (2 ^ eoff) 1 hP hΓy hΓ
  rw [mul_one, mul_one] at hsc
  have hjmb : |value jm.toBits| ≤ 200 := by rw [hjm, abs_zero]; norm_num
  exact finish_pos p1 p2 jm eoff (Real.Gamma v) (value p1.toBits + value p2.toBits) A
    (17 / 2 ^ 63) hp1 hp2 hjmf hjmb hp2r (by rw [sub_self, abs_zero]; positivity) (by norm_num)
    (by norm_num) hPA hsc
    (by rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 800 ≤ 1 / 17)])
    (by rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (121 : ℝ) ≤ 2 ^ 800)]) he
    (gamma_le_max hT x hx (by linarith) ht)

#print axioms poly_facts
#print axioms gamma_le_max
#print axioms down_case
#print axioms zero_case

end Library.Numerics.Float64.Tgamma.TgammaAccDownCase
