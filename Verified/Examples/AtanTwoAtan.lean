import Verified.Examples.AtanTwoErr

/-!
`Atan.atan q` for the rounded quotient `q = |y/x|` of `Atan.atan2`, against `arctan Q` for the
exact quotient `Q`: every branch of `atan` gives `AtanTwoErr.Good`.  The reduced branches use the
error bounds of `AtanTheoremCases` and the polynomial branch those of `AtanTheoremSmall`.  Below
`2 ^ -27` the result is `q`, which meets the relative criterion down to `2 ^ -1021` and the
criterion of the uniform grid of spacing `2 ^ -1074` below.
-/

namespace Verified.Examples.AtanTwoAtan
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AtanTheoremCases AtanTheoremSmall
  AtanTheorem AtanTheoremPoly AtanTwoErr

set_option exponentiation.threshold 4096

theorem arctan_nonneg (v : ℝ) (hv : 0 ≤ v) : 0 ≤ Real.arctan v := by
  have := Real.arctan_mono hv
  rwa [Real.arctan_zero] at this

theorem case_range (z : Float) (v Q E L H : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2046)
    (hQ0 : 0 ≤ Q) (hqQ : |v - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075)
    (hL0 : 0 ≤ L) (hL : L ≤ v) (hH : v + 1 / 2 ^ 1075 ≤ H * (1 - 1 / 2 ^ 53))
    (hzf : Finite z.toBits) (hE : |value z.toBits - Real.arctan v| ≤ E)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + E + 1 / 2 ^ 52 ≤ Real.arctan v)
    (hs1 : H / (1 + L * H) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 53)
    (hEs : E + (H / (1 + L * H) / 2 ^ 53 + 1 / 2 ^ 1075) <
      5 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) / 2)
    (hD : E + (H / (1 + L * H) / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 149 / 100 / 2 ^ 52) :
    Good z Q := by
  have hQH : Q ≤ H := by
    have := (q_bounds v Q hqQ).1
    nlinarith
  exact finish_case z v Q E _ n hn1 hn hzf hE (sens_range v Q L H hL0 hL hQ0 hQH hqQ) hs1 hB
    hEs hD

theorem case_sharp (z : Float) (v Q E L c : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2046)
    (hQ0 : 0 ≤ Q) (hqQ : |v - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075) (hL1 : 1 ≤ L) (hL : L ≤ v)
    (hc : L + c / 2 ^ 53 + 1 / 2 ^ 1075 ≤ c * (1 + L ^ 2)) (hc2 : 1 ≤ 2 * c * L)
    (hzf : Finite z.toBits) (hE : |value z.toBits - Real.arctan v| ≤ E)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + E + 1 / 2 ^ 52 ≤ Real.arctan v)
    (hs1 : c / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 53)
    (hEs : E + (c / 2 ^ 53 + 1 / 2 ^ 1075) < 5 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) / 2)
    (hD : E + (c / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 149 / 100 / 2 ^ 52) :
    Good z Q :=
  finish_case z v Q E _ n hn1 hn hzf hE (sens_sharp v Q L c hL1 hL hQ0 hqQ hc hc2) hs1 hB hEs hD

/-- `|q| ≥ 2 ^ 66`: the result is `atanhi[3] + atanlo[3]`, which rounds to `atanhi[3]`. -/
theorem big_case (q : Float) (hq : Finite q.toBits) (hsq : Wasm.IEEE64.sign q.toBits = false)
    (Q : ℝ) (hqQ : |value q.toBits - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075)
    (h1 : ixOf q ≥ 0x44100000) : Good (Atan.atan q) Q := by
  have hv0 := nonneg_of_sign _ hsq
  have hge : 2 ^ 66 ≤ |value q.toBits| :=
    not_lt.mp (fun h => u_not_lt_of_ge _ _ h1 ((ix_66 q).mpr h))
  rw [abs_of_nonneg hv0] at hge
  have hQu := (q_bounds _ _ hqQ).2
  have hQ1 : 2 ^ 65 ≤ Q := by linarith
  have hQp : 0 < Q := lt_of_lt_of_le (by positivity) hQ1
  have heq : Atan.atan q =
      Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07 := by
    rw [atan_big_eq q hq h1, F64UpperWord.sign_test, hsq]
    simp only [Bool.false_eq_true, ite_false]
  rw [heq]
  unfold Good
  rw [big_bits]
  have hinv := Real.arctan_inv_of_pos hQp
  have hi0 : 0 ≤ Real.arctan Q⁻¹ := arctan_nonneg _ (inv_nonneg.mpr hQp.le)
  have hi1 : Real.arctan Q⁻¹ ≤ 1 / 2 ^ 65 := by
    have := AtanTheoremConst.abs_arctan_le Q⁻¹
    rw [abs_of_nonneg hi0, abs_of_nonneg (inv_nonneg.mpr hQp.le)] at this
    refine this.trans ?_
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hQ1
  have hc := big_close
  have hp := AtanTheoremConst.pi_close
  rw [abs_le] at hc hp
  have herr : |value 0x3FF921FB54442D18 - Real.arctan Q| ≤ 62 / 10 ^ 18 + 1 / 2 ^ 65 := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  have hf : Finite (0x3FF921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  refine ⟨hf, herr.trans (by norm_num), ?_⟩
  refine F64TwoSteps.within_two_of_error _ _ 1023 (by norm_num) (by norm_num) _ hf herr ?_
    (by norm_num)
  rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
  norm_num
  linarith [hp.1, hp.2]

/-- `q < 2 ^ -27`: the result is `q`. -/
theorem tiny_case (q : Float) (hq : Finite q.toBits) (hsq : Wasm.IEEE64.sign q.toBits = false)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hqQ : |value q.toBits - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075)
    (hs : value q.toBits < 1 / 2 ^ 27) : Good q Q := by
  have hq63 : q.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hsq
    exact hsq
  obtain ⟨hQl, hQu⟩ := q_bounds (value q.toBits) Q hqQ
  have hQ1 : Q ≤ 10001 / 10000 / 2 ^ 27 := by linarith
  have hQ2 : Q ^ 2 ≤ 5002 / 10000 / 2 ^ 53 := by
    nlinarith [mul_le_mul hQ1 hQ1 hQ0 (by positivity)]
  have hnear := AtanTheoremSmall.arctan_near Q (by rw [abs_of_nonneg hQ0]; linarith)
  rw [abs_of_nonneg hQ0] at hnear
  have hcube : Q ^ 3 / (1 - Q ^ 2) ≤ 51 / 100 / 2 ^ 53 * Q := by
    rw [div_le_iff₀ (by nlinarith)]
    have h3 : Q ^ 3 = Q * Q ^ 2 := by ring
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left hQ2 hQ0]
  have hn' := abs_le.mp hnear
  have hqQ' := abs_le.mp hqQ
  have htot : |value q.toBits - Real.arctan Q| ≤ 151 / 100 / 2 ^ 53 * Q + 1 / 2 ^ 1075 := by
    rw [abs_le]
    constructor <;> linarith [hn'.1, hn'.2, hqQ'.1, hqQ'.2]
  have hat0 := arctan_nonneg Q hQ0
  refine ⟨hq, htot.trans (by linarith), ?_⟩
  rcases le_or_gt (1 / 2 ^ 1021) Q with hQb | hQb
  · obtain ⟨n, hn2, hn, hX, hX2⟩ := F64RoundNearest.binade_of_real Q hQb (by linarith)
    refine F64TwoSteps.within_two_rel _ _ Q n hn2 (by omega) hX hX2 (1 / 2 ^ 52)
      (205 / 100 / 2 ^ 53) (by positivity) (by positivity) hq ?_ ?_ (by norm_num) (by norm_num)
    · refine htot.trans ?_
      linarith
    · linarith [hn'.1]
  · refine F64TwoSteps.within_two_low _ _ hq hq63 (by linarith) hat0 ?_ ?_
    · have := AtanTheoremConst.abs_arctan_le Q
      rw [abs_of_nonneg hat0, abs_of_nonneg hQ0] at this
      linarith
    · calc |value q.toBits - Real.arctan Q| ≤ 151 / 100 / 2 ^ 53 * Q + 1 / 2 ^ 1075 := htot
        _ < 5 / 2 / 2 ^ 1074 := by linarith

/-- `2 ^ -27 ≤ q ≤ 1/4`: the relative criterion on the binade of `Q`. -/
theorem small_case (q : Float) (hq : Finite q.toBits) (hv0 : 0 ≤ value q.toBits) (Q : ℝ)
    (hQ0 : 0 ≤ Q) (hqQ : |value q.toBits - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075)
    (h1 : 1 / 2 ^ 27 ≤ value q.toBits) (h2 : value q.toBits ≤ 1 / 4) :
    Good (q - q * atanS q) Q := by
  have hav : |value q.toBits| = value q.toBits := abs_of_nonneg hv0
  obtain ⟨hzf, hE⟩ := atan_poly_small_err q hq (by rw [hav]; exact h1) (by rw [hav]; exact h2)
  rw [hav] at hE
  obtain ⟨hQl, hQu⟩ := q_bounds (value q.toBits) Q hqQ
  have hQ1 : Q ≤ 2501 / 10000 := by linarith
  have hQ2 : 99 / 100 / 2 ^ 27 ≤ Q := by linarith
  have hs := sens_crude (value q.toBits) Q hv0 hQ0 hqQ
  have hE' := abs_le.mp hE
  have hs' := abs_le.mp hs
  have htot : |value (q - q * atanS q).toBits - Real.arctan Q| ≤ 221 / 100 / 2 ^ 53 * Q := by
    rw [abs_le]
    constructor <;> linarith [hE'.1, hE'.2, hs'.1, hs'.2]
  have hnear := AtanTheoremSmall.arctan_near Q (by rw [abs_of_nonneg hQ0]; linarith)
  rw [abs_of_nonneg hQ0] at hnear
  have hQQ := mul_le_mul hQ1 hQ1 hQ0 (by norm_num)
  have hcube : Q ^ 3 / (1 - Q ^ 2) ≤ Q / 14 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hQQ hQ0]
  refine ⟨hzf, htot.trans (by linarith), ?_⟩
  obtain ⟨n, hn2, hn, hX, hX2⟩ := F64RoundNearest.binade_of_real Q (by linarith) (by linarith)
  exact F64TwoSteps.within_two_rel _ _ Q n hn2 (by omega) hX hX2 (1 / 14) (221 / 100 / 2 ^ 53)
    (by norm_num) (by positivity) hzf htot (by linarith [(abs_le.mp hnear).1]) (by norm_num)
    (by norm_num)

/-- Every branch of `atan` for a nonnegative finite `q`. -/
theorem atan_good (q : Float) (hq : Finite q.toBits) (hsq : Wasm.IEEE64.sign q.toBits = false)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hqQ : |value q.toBits - Q| ≤ Q / 2 ^ 53 + 1 / 2 ^ 1075) :
    Good (Atan.atan q) Q := by
  have hv0 : 0 ≤ value q.toBits := nonneg_of_sign _ hsq
  have hav : |value q.toBits| = value q.toBits := abs_of_nonneg hv0
  have hneg : (q.toBits >>> 32 >>> 31 == 1) = false := by rw [F64UpperWord.sign_test, hsq]
  by_cases h1 : ixOf q ≥ 0x44100000
  · exact big_case q hq hsq Q hqQ h1
  by_cases h2 : ixOf q < 0x3e400000
  · have hs := (ix_27 q).mp h2
    rw [atan_tiny_eq q h2 (huge_gt q hq (hs.trans (by norm_num)))]
    rw [hav] at hs
    exact tiny_case q hq hsq Q hQ0 hqQ hs
  have hge : 1 / 2 ^ 27 ≤ |value q.toBits| := not_lt.mp (fun h => h2 ((ix_27 q).mpr h))
  rw [hav] at hge
  by_cases h3 : ixOf q < 0x3fdc0000
  · rw [atan_poly_eq q h1 h2 h3]
    have hlt := (ix_a q).mp h3
    rw [hav] at hlt
    rcases le_or_gt (value q.toBits) (1 / 4) with ha | ha
    · exact small_case q hq hv0 Q hQ0 hqQ hge ha
    rcases le_or_gt (value q.toBits) (2556 / 10000) with hb | hb
    · obtain ⟨hzf, hE, hB⟩ := atan_poly_mid_a_err q hq (by rw [hav]; exact ha.le)
        (by rw [hav]; exact hb)
      rw [abs_of_nonneg (arctan_nonneg (value q.toBits) hv0)] at hB
      exact case_range _ _ Q _ (1 / 4) (25561 / 100000) 1020 (by norm_num) (by norm_num) hQ0 hqQ
        (by norm_num) ha.le (by linarith) hzf hE hB (by norm_num) (by norm_num) (by norm_num)
    · obtain ⟨hzf, hE, hB⟩ := atan_poly_mid_b_err q hq (by rw [hav]; exact hb.le)
        (by rw [hav]; exact hlt.le)
      rw [abs_of_nonneg (arctan_nonneg (value q.toBits) hv0)] at hB
      exact case_range _ _ Q _ (2556 / 10000) (43751 / 100000) 1021 (by norm_num) (by norm_num)
        hQ0 hqQ (by norm_num) hb.le (by linarith) hzf hE hB (by norm_num) (by norm_num)
        (by norm_num)
  have hA : 7 / 16 ≤ value q.toBits := by
    have := not_lt.mp (fun h => h3 ((ix_a q).mpr h))
    rwa [hav] at this
  by_cases h4 : ixOf q < 0x3ff30000
  · have hc := (ix_c q).mp h4
    rw [hav] at hc
    by_cases h5 : ixOf q < 0x3fe60000
    · have hb := (ix_b q).mp h5
      rw [hav] at hb
      rw [atan_tail0_eq q h1 h3 h4 h5]
      simp only [hneg, Bool.false_eq_true, ite_false]
      rcases le_or_gt (value q.toBits) (551 / 1000) with hm | hm
      · obtain ⟨hzf, hE, hB⟩ := case0_low_err q hq (by rw [hav]; exact hA) (by rw [hav]; exact hm)
        rw [hav] at hE hB
        exact case_range _ _ Q _ (7 / 16) (5512 / 10000) 1021 (by norm_num) (by norm_num) hQ0
          hqQ (by norm_num) hA (by linarith) hzf hE hB (by norm_num) (by norm_num) (by norm_num)
      · obtain ⟨hzf, hE, hB⟩ := case0_high_err q hq (by rw [hav]; exact hm.le)
          (by rw [hav]; exact hb.le)
        rw [hav] at hE hB
        exact case_range _ _ Q _ (551 / 1000) (6877 / 10000) 1022 (by norm_num) (by norm_num)
          hQ0 hqQ (by norm_num) hm.le (by linarith) hzf hE hB (by norm_num) (by norm_num)
          (by norm_num)
    · have hB' : 11 / 16 ≤ value q.toBits := by
        have := not_lt.mp (fun h => h5 ((ix_b q).mpr h))
        rwa [hav] at this
      rw [atan_tail1_eq q h1 h3 h4 h5]
      simp only [hneg, Bool.false_eq_true, ite_false]
      rcases le_or_gt (value q.toBits) 1 with hm | hm
      · obtain ⟨hzf, hE, hB⟩ := case1_low_err q hq (by rw [hav]; exact hB')
          (by rw [hav]; exact hm)
        rw [hav] at hE hB
        exact case_range _ _ Q _ (11 / 16) (10001 / 10000) 1022 (by norm_num) (by norm_num)
          hQ0 hqQ (by norm_num) hB' (by linarith) hzf hE hB (by norm_num) (by norm_num)
          (by norm_num)
      · obtain ⟨hzf, hE, hB⟩ := case1_high_err q hq (by rw [hav]; exact hm.le)
          (by rw [hav]; exact hc.le)
        rw [hav] at hE hB
        exact case_range _ _ Q _ 1 (11876 / 10000) 1022 (by norm_num) (by norm_num)
          hQ0 hqQ (by norm_num) hm.le (by linarith) hzf hE hB (by norm_num) (by norm_num)
          (by norm_num)
  · have hC : 19 / 16 ≤ value q.toBits := by
      have := not_lt.mp (fun h => h4 ((ix_c q).mpr h))
      rwa [hav] at this
    by_cases h6 : ixOf q < 0x40038000
    · have hd := (ix_d q).mp h6
      rw [hav] at hd
      rw [atan_tail2_eq q h1 h3 h4 h6]
      simp only [hneg, Bool.false_eq_true, ite_false]
      rcases le_or_gt (value q.toBits) (3 / 2) with hm | hm
      · obtain ⟨hzf, hE, hB⟩ := case2_a_err q hq (by rw [hav]; exact hC) (by rw [hav]; exact hm)
        rw [hav] at hE hB
        exact case_range _ _ Q _ (19 / 16) (15001 / 10000) 1022 (by norm_num) (by norm_num)
          hQ0 hqQ (by norm_num) hC (by linarith) hzf hE hB (by norm_num) (by norm_num)
          (by norm_num)
      rcases le_or_gt (value q.toBits) (793 / 500) with hm2 | hm2
      · obtain ⟨hzf, hE, hB⟩ := case2_b_err q hq (by rw [hav]; exact hm.le)
          (by rw [hav]; exact hm2)
        rw [hav] at hE hB
        exact case_range _ _ Q _ (3 / 2) (15861 / 10000) 1022 (by norm_num) (by norm_num)
          hQ0 hqQ (by norm_num) hm.le (by linarith) hzf hE hB (by norm_num) (by norm_num)
          (by norm_num)
      · obtain ⟨hzf, hE, hB⟩ := case2_c_err q hq (by rw [hav]; exact hm2.le)
          (by rw [hav]; exact hd.le)
        rw [hav] at hE hB
        exact case_sharp _ _ Q _ (793 / 500) (4512 / 10000) 1023 (by norm_num) (by norm_num)
          hQ0 hqQ (by norm_num) hm2.le (by norm_num) (by norm_num) hzf hE hB (by norm_num)
          (by norm_num) (by norm_num)
    · have hD : 39 / 16 ≤ value q.toBits := by
        have := not_lt.mp (fun h => h6 ((ix_d q).mpr h))
        rwa [hav] at this
      have hlt66 : |value q.toBits| < 2 ^ 66 := (ix_66 q).mp (u_lt_of_not_ge _ _ h1)
      rw [hav] at hlt66
      rw [atan_tail3_eq q h1 h3 h4 h6]
      simp only [hneg, Bool.false_eq_true, ite_false]
      obtain ⟨hzf, hE, hB⟩ := case3_err q hq (by rw [hav]; exact hD) (by rw [hav]; linarith)
      rw [hav] at hE hB
      exact case_sharp _ _ Q _ (39 / 16) (3512 / 10000) 1023 (by norm_num) (by norm_num)
        hQ0 hqQ (by norm_num) hD (by norm_num) (by norm_num) hzf hE hB (by norm_num)
        (by norm_num) (by norm_num)

#print axioms atan_good

end Verified.Examples.AtanTwoAtan
