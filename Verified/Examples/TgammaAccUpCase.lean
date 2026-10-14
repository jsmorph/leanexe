import Verified.Examples.TgammaAccFinish
import Verified.Examples.TgammaAccPre

/-!
The case `x < j` of the accurate path of `Tgamma` from `1/4`: `j = 4`, `-184 < x < 4`, and the loop
forms `W = x (x + 1) ⋯ (x + M)` divided by `2 ^ (500 r)`, with `M + 1 = 4 - ⌊x⌋` factors.  Then
`Γ x = Γ (x + M + 1) / (W 2 ^ (500 r))`, the code divides the polynomial by `wh + wl`, and the scale
word is `eoff - 500 r`, which is `eoff` for `r = 0` and the two's complement of `500 r - eoff` from
`r = 1` on (`up_case`).  `|W| ≥ 2 ^ -57` and `|x + i| ≤ 2 ^ 8` bound `r` by 3.
-/

namespace Verified.Examples.TgammaAccUpCase
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAccUp TgammaAccFin
  TgammaAccCrr TgammaAccBounds TgammaAccFinish

set_option exponentiation.threshold 4096

theorem eoff_zero (a : ℕ) : UInt64.ofNat a - 500 * UInt64.ofNat 0 = UInt64.ofNat a := by
  simp

theorem eoff_neg (a r : ℕ) (h : a ≤ 500 * r) :
    UInt64.ofNat a - 500 * UInt64.ofNat r = 0 - UInt64.ofNat (500 * r - a) := by
  have h1 : UInt64.ofNat (500 * r - a) + UInt64.ofNat a = 500 * UInt64.ofNat r := by
    rw [← UInt64.ofNat_add, Nat.sub_add_cancel h, UInt64.ofNat_mul]
    rfl
  rw [← h1]
  abel

/-- **The path for `x < j`.** -/
theorem up_case (hF : FmaSpec.FmaNearest) (hGap : TgammaRefl4.SubnormalGap) (x : Float)
    (hnint : ∀ n : ℤ, value x.toBits ≠ n) (hv54 : ∀ n : ℤ, 1 / 2 ^ 54 ≤ |value x.toBits + n|)
    (hlo : -184 < value x.toBits) (M : ℕ) (hM : M ≤ 187) (hhi : value x.toBits + M < 4)
    (hy4 : 4 ≤ value x.toBits + (M + 1 : ℕ)) (eoff : ℕ) (he : eoff ≤ 3) (A : ℝ)
    (hA1 : 1 / 17 ≤ A)
    (hΓ : |Real.Gamma (value x.toBits + (M + 1 : ℕ)) - 2 ^ eoff * A| ≤
      1 / 2 ^ 62 * Real.Gamma (value x.toBits + (M + 1 : ℕ)))
    (p1 p2 : Float) (hp1 : Finite p1.toBits) (hp2 : Finite p2.toBits)
    (hpA : |value p1.toBits + value p2.toBits - A| ≤ 1 / 2 ^ 63)
    (hp1b : |value p1.toBits| ≤ 120) (hp2b : |value p2.toBits| ≤ 1 / 2 ^ 37)
    (wh wl : Float) (hwhf : Finite wh.toBits) (hwlf : Finite wl.toBits) (r : ℕ)
    (hWe : |value wh.toBits + value wl.toBits - W (value x.toBits) r M| ≤
      M / 2 ^ 95 * |W (value x.toBits) r M|)
    (hwlb : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 50) (hwhb : |value wh.toBits| ≤ 2 ^ 518)
    (hS : S (value x.toBits) M / 4 ≤ |W (value x.toBits) r M|)
    (jm : Float) (hjmf : Finite jm.toBits) (hjm : value jm.toBits = M + 1) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (Float.ofBits (finRes
        (mulDD3 p1 p2 (1.0 / wh)
          ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).1
        (adjLow
          (mulDD3 p1 p2 (1.0 / wh)
            ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).1
          (mulDD3 p1 p2 (1.0 / wh)
            ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh))).2 jm)
        (UInt64.ofNat eoff - 500 * UInt64.ofNat r))).toBits := by
  set v := value x.toBits with hvdef
  set Wv := W v r M with hWvdef
  have hP : (0 : ℝ) < 2 ^ eoff := by positivity
  -- the product
  have hS55 : 1 / 2 ^ 55 ≤ S v M := prod_small v hv54 M
  have hW57 : 1 / 2 ^ 57 ≤ |Wv| := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 57 = 1 / 2 ^ 55 / 4)]
  have hWp : 0 < |Wv| := lt_of_lt_of_le (by positivity) hW57
  have hW0 : Wv ≠ 0 := abs_pos.mp hWp
  have hβ : (M : ℝ) / 2 ^ 95 ≤ 187 / 2 ^ 95 := by
    have : (M : ℝ) ≤ 187 := by exact_mod_cast hM
    exact div_le_div_of_nonneg_right this (by positivity)
  have hWe' : |value wh.toBits + value wl.toBits - Wv| ≤ 187 / 2 ^ 95 * |Wv| :=
    hWe.trans (mul_le_mul_of_nonneg_right hβ (abs_nonneg _))
  set Wd := value wh.toBits + value wl.toBits with hWddef
  have hWd1 : |Wv| / 2 ≤ |Wd| := by
    have h1 := abs_sub_abs_le_abs_sub Wv Wd
    rw [abs_sub_comm] at h1
    linarith [(by norm_num : (187 : ℝ) / 2 ^ 95 ≤ 1 / 2)]
  have hW520 : |Wv| ≤ 2 ^ 520 := by
    have h1 := abs_sub_abs_le_abs_sub Wv Wd
    have h2 := abs_add_le (value wh.toBits) (value wl.toBits)
    rw [abs_sub_comm] at h1
    linarith [(by norm_num : (187 : ℝ) / 2 ^ 95 ≤ 1 / 2),
      (by norm_num : (2 : ℝ) ^ 518 + 2 ^ 518 / 2 ^ 50 ≤ 2 ^ 520 / 2)]
  have hwh1 : 1 / 2 ^ 60 ≤ |value wh.toBits| := by
    have h2 := abs_add_le (value wh.toBits) (value wl.toBits)
    have h3 : |value wh.toBits| / 2 ^ 50 ≤ |value wh.toBits| :=
      div_le_self (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1 / 2 ^ 57 / 2 / 2)]
  have hwh2 : |value wh.toBits| ≤ 2 ^ 519 := by
    linarith [(by norm_num : (2 : ℝ) ^ 518 ≤ 2 ^ 519)]
  -- the polynomial
  set P := value p1.toBits + value p2.toBits with hPdef
  have hPA2 := abs_le.mp hpA
  have hPab := abs_add_le (value p1.toBits) (value p2.toBits)
  have hA121 : A ≤ 121 := by
    have := le_abs_self P
    linarith [(by norm_num : (120 : ℝ) + 1 / 2 ^ 37 + 1 / 2 ^ 63 ≤ 121)]
  have hp1lo : 1 / 32 ≤ |value p1.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub P (value p2.toBits)
    rw [show P - value p2.toBits = value p1.toBits by rw [hPdef]; ring] at h1
    have h2 := le_abs_self P
    linarith [(by norm_num : (1 : ℝ) / 32 ≤ 1 / 17 - 1 / 2 ^ 63 - 1 / 2 ^ 37)]
  have hp2r : |value p2.toBits| ≤ |value p1.toBits| / 2 ^ 30 := by
    have : (1 : ℝ) / 32 / 2 ^ 30 ≤ |value p1.toBits| / 2 ^ 30 :=
      div_le_div_of_nonneg_right hp1lo (by positivity)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 37 ≤ 1 / 32 / 2 ^ 30)]
  -- the quotient
  obtain ⟨hf1f, hf2f, hfq, hf2r⟩ := TgammaAccComb.div_step hF p1 p2 wh wl hp1 hp2 hwhf hwlf hp2r
    hp1lo (by linarith [(by norm_num : (120 : ℝ) ≤ 2 ^ 8)]) hwlb hwh1 hwh2
  set f := mulDD3 p1 p2 (1.0 / wh)
    ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh)) with hfdef
  have hf2r30 : |value f.2.toBits| ≤ |value f.1.toBits| / 2 ^ 30 :=
    hf2r.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num))
  have hPA : |P - A| ≤ 17 / 2 ^ 63 * |A| := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < A)]
    linarith
  have hQ := rel_div P A Wd Wv (17 / 2 ^ 63) (187 / 2 ^ 95) hW0 (by norm_num) (by norm_num)
    (by norm_num) hPA hWe'
  have hε : (17 / 2 ^ 63 + 187 / 2 ^ 95) * (1 + 2 * (187 / 2 ^ 95)) ≤ (18 : ℝ) / 2 ^ 63 := by
    norm_num
  have hε0 : (0 : ℝ) ≤ (17 / 2 ^ 63 + 187 / 2 ^ 95) * (1 + 2 * (187 / 2 ^ 95)) := by norm_num
  have hQ01 : 1 / 2 ^ 800 ≤ |A / Wv| := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < A), le_div_iff₀ hWp]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 800 * 2 ^ 520 ≤ 1 / 17)]
  have hQ02 : |A / Wv| ≤ 2 ^ 800 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < A), div_le_iff₀ hWp]
    linarith [(by norm_num : (121 : ℝ) ≤ 2 ^ 800 * (1 / 2 ^ 57))]
  -- `Γ`
  have hNP : GammaBasic.NotPole v := GammaBasic.notPole_of_not_int hnint
  have hprod := GammaBasic.gamma_add_nat hNP (M + 1)
  have hWprod : Wv * 2 ^ (500 * r) = ∏ j ∈ Finset.range (M + 1), (v + (j : ℝ)) := by
    rw [hWvdef, W, div_mul_cancel₀ _ (by positivity)]
  set Γy := Real.Gamma (v + ((M + 1 : ℕ) : ℝ)) with hΓydef
  have hΓy : 0 < Γy := Real.Gamma_pos_of_pos (by linarith)
  have hΓv : Real.Gamma v * (Wv * 2 ^ (500 * r)) = Γy := by rw [hWprod, ← hprod]
  have hsc := scale_rel A Γy (2 ^ eoff) (1 / Wv) hP hΓy hΓ
  have hQ0 : A / Wv = A * (1 / Wv) := by ring
  have hjmb : |value jm.toBits| ≤ 200 := by
    rw [hjm, abs_of_pos (by positivity)]
    have : (M : ℝ) ≤ 187 := by exact_mod_cast hM
    linarith
  -- the number of divisions by `2 ^ 500`
  have hprodb : |∏ j ∈ Finset.range (M + 1), (v + (j : ℝ))| ≤ 2 ^ (8 * (M + 1)) := by
    rw [Finset.abs_prod]
    calc ∏ j ∈ Finset.range (M + 1), |v + (j : ℝ)| ≤ ∏ _j ∈ Finset.range (M + 1), (2 : ℝ) ^ 8 := by
          apply Finset.prod_le_prod (fun j _ => abs_nonneg _)
          intro j hj
          have hj' : (j : ℝ) ≤ M := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          rw [abs_le]
          constructor <;> linarith
      _ = 2 ^ (8 * (M + 1)) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]
  have hr3 : r ≤ 3 := by
    by_contra hc
    have h1 : |Wv| * 2 ^ (500 * r) ≤ 2 ^ (8 * (M + 1)) := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (500 * r)), ← abs_mul, hWprod]
      exact hprodb
    have h2 : (2 : ℝ) ^ (8 * (M + 1)) ≤ 2 ^ 1504 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ 2000 ≤ 2 ^ (500 * r) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : 1 / 2 ^ 57 * 2 ^ 2000 ≤ |Wv| * 2 ^ (500 * r) :=
      mul_le_mul hW57 h3 (by positivity) (abs_nonneg _)
    linarith [(by norm_num : (2 : ℝ) ^ 1504 < 1 / 2 ^ 57 * 2 ^ 2000)]
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · -- no division: the scale `eoff`
    subst hr0
    rw [eoff_zero]
    have hΓv0 : Real.Gamma v * Wv = Γy := by rw [← hΓv]; simp
    have hg : Γy * (1 / Wv) / 2 ^ eoff = Real.Gamma v / 2 ^ eoff := by
      rw [← hΓv0, mul_assoc, mul_one_div_cancel hW0, mul_one]
    rw [← hQ0, hg] at hsc
    have hgb : |Real.Gamma v / 2 ^ eoff| ≤ 2 * |A / Wv| := by
      have h1 := abs_sub_abs_le_abs_sub (Real.Gamma v / 2 ^ eoff) (A / Wv)
      rw [abs_sub_comm] at h1
      have h2 : |Real.Gamma v / 2 ^ eoff| / 2 ^ 62 ≤ |Real.Gamma v / 2 ^ eoff| / 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith
    have hG2 : |Real.Gamma v| ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50) := by
      rw [abs_div, abs_of_pos hP] at hgb
      have h8 : (2 : ℝ) ^ eoff ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) he
      have h1 : |Real.Gamma v| ≤ 2 * |A / Wv| * 2 ^ eoff := (div_le_iff₀ hP).mp hgb
      have h2 : 2 * |A / Wv| * 2 ^ eoff ≤ 2 * 2 ^ 800 * 2 ^ 3 :=
        mul_le_mul (by linarith) h8 hP.le (by positivity)
      linarith [(by norm_num : (2 : ℝ) * 2 ^ 800 * 2 ^ 3 ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50))]
    exact finish_pos f.1 f.2 jm eoff (Real.Gamma v) (P / Wd) (A / Wv) _ hf1f hf2f hjmf hjmb
      hf2r30 hfq hε0 hε hQ hsc hQ01 hQ02 (by omega) hG2
  · -- `r` divisions: the scale `-(500 r - eoff)`
    rw [eoff_neg eoff r (by omega)]
    have hpow : (2 : ℝ) ^ (500 * r) = 2 ^ (500 * r - eoff) * 2 ^ eoff := by
      rw [← pow_add]
      congr 1
      omega
    have hg : Γy * (1 / Wv) / 2 ^ eoff = Real.Gamma v * 2 ^ (500 * r - eoff) := by
      rw [← hΓv, hpow]
      field_simp <;> ring
    rw [← hQ0, hg] at hsc
    exact finish_neg f.1 f.2 jm (500 * r - eoff) (Real.Gamma v) (P / Wd) (A / Wv) _ hf1f hf2f
      hjmf hjmb hf2r hfq hε0 hε hQ hsc hQ01 hQ02 (by omega) (by omega)
      (Real.Gamma_ne_zero hNP)
      (acc_gap hGap x hnint hlo (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]))

#print axioms eoff_neg
#print axioms up_case

end Verified.Examples.TgammaAccUpCase
