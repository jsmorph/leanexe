import Library.Numerics.Float64.Lgamma.LgammaStirTop
import Library.Numerics.Float64.Lgamma.LgammaLogd
import Library.Numerics.Float64.Lgamma.LgammaFastWalk

/-!
The two branches of the fast path's Stirling series of `Lgamma.lgammaWith` from `2^800` to the
threshold `x1 = 0x1.754d9278b51a6p+1014`.  The code takes `p = (lh - 1, ll)` from `asLogd` below
`va = 0x1.754cp+1014` (`pair_low`) and normalizes it with `fastTwoSum` from there (`pair_high`), so
that the low part lies within `2^-44` (`Library.Numerics.Float64.Tgamma.TgammaDDTop.fts_half`).  In both branches `p1 x` stays
below `2^1024 - 13 · 2^968`, which a kernel check of `x (log x - 1 + δ)` at `va` and at `x1` with
the bound on `log x1` of `GammaThresholds` confirms, and `stir_top_core` gives `LeafTop`
(`leaf_low`, `leaf_high`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaFastTop
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaWords LgammaPiecePoly
  LgammaStirTop GammaThresholds RatExpLog LgammaFastSmall

set_option exponentiation.threshold 4096

/-- `0x1.754cp+1014`, where the code starts to normalize `log x - 1`. -/
def va : ℚ := 0x1754c000000000 * 2 ^ 962

/-- The upper bound on `log x1` of `GammaThresholds.lgamma_x1`. -/
def logX1Hi : ℚ := 1014 * log2Hi + 29885894554980044821209402395 / 2 ^ 96

theorem log_x1_le : Real.log (x1 : ℝ) ≤ logX1Hi := by
  have hl := log_huge (m := 0x1754d9278b51a6) (by norm_num)
    (478174312879680717139350438317 / 2 ^ 100) (29885894554980044821209402395 / 2 ^ 96)
    (le_log _ _ 40 (by norm_num) (by decide +kernel) (by decide +kernel))
    (log_le _ _ 40 (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel))
  have h := hl.2
  rw [show ((0x1754d9278b51a6 * 2 ^ 962 : ℚ) : ℝ) = (x1 : ℝ) by rw [x1]] at h
  rw [logX1Hi]
  push_cast at h ⊢
  exact h

/-- The products of the two branches stay below `2^1024 - 13 · 2^968`. -/
theorem products_ok :
    (va : ℚ) * (logX1Hi - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) ≤ 2 ^ 1024 - 13 * 2 ^ 968 ∧
      (x1 : ℚ) * (logX1Hi - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) ≤ 2 ^ 1024 - 13 * 2 ^ 968 := by
  decide +kernel

theorem va_le_x1 : va ≤ x1 := by decide +kernel

/-- The pair `(lh - 1, ll)` of `asLogd` near `log x - 1`. -/
theorem logd_pair (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact) (ax : Float)
    (hax : Finite ax.toBits) (h800 : 2 ^ 800 ≤ value ax.toBits)
    (hvx : value ax.toBits ≤ x1) (L0 : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable ax) :
    Finite (L0.1 - 1.0).toBits ∧ Finite L0.2.toBits ∧
      |value (L0.1 - 1.0).toBits + value L0.2.toBits - (Real.log (value ax.toBits) - 1)| ≤
        1 / 2 ^ 67 ∧
      |value L0.2.toBits| ≤ 1 / 2 ^ 21 ∧ 550 ≤ value (L0.1 - 1.0).toBits ∧
      value (L0.1 - 1.0).toBits ≤ 705 ∧ Real.log (value ax.toBits) ≤ logX1Hi := by
  set v := value ax.toBits with hvdef
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) h800
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hg1 : (554 : ℝ) ≤ Real.log v := by
    have h1 := Real.log_le_log (by positivity) h800
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hgx : Real.log v ≤ logX1Hi := (Real.log_le_log hv0 hvx).trans log_x1_le
  have hx1h : (logX1Hi : ℝ) ≤ 704 := by
    have : logX1Hi ≤ 704 := by decide +kernel
    exact_mod_cast this
  obtain ⟨hlf, hllf, herr, hllb⟩ := LgammaLogd.asLogd_spec hF hL ax hax hv0
  rw [← hL0] at hlf hllf herr hllb
  set g := Real.log v with hgdef
  set lh := value L0.1.toBits with hlhdef
  set ll := value L0.2.toBits with hlldef
  have hgabs : |g| = g := abs_of_pos (by linarith)
  rw [hgabs] at herr
  have herr' : |lh + ll - g| ≤ 1 / 2 ^ 67 := by
    have : g / 2 ^ 78 ≤ 704 / 2 ^ 78 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 69 + 704 / 2 ^ 78 ≤ 1 / 2 ^ 67)]
  have hlh1 : |lh| ≤ 706 := by
    have h1 := abs_le_three lh ll g
    rw [hgabs] at h1
    linarith
  have hll : |ll| ≤ 1 / 2 ^ 21 := by
    have : |lh| / 2 ^ 52 ≤ 706 / 2 ^ 52 := div_le_div_of_nonneg_right hlh1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 706 / 2 ^ 52 ≤ 1 / 2 ^ 21)]
  obtain ⟨hlmf, hlmv⟩ := LgammaStir.sub_small_exact L0.1 1.0 hlf LgammaSpecial.one_finite 0
    (by norm_num) (by rw [LgammaSpecial.one_value]; norm_num)
    (by have := abs_le.mp herr'; have := abs_le.mp hll; linarith)
    (by have := abs_le.mp herr'; have := abs_le.mp hll
        linarith [(by norm_num : (706 : ℝ) < 2 ^ 52)])
  rw [LgammaSpecial.one_value] at hlmv
  refine ⟨hlmf, hllf, ?_, hll, ?_, ?_, hgx⟩
  · rw [hlmv, show lh - 1 + ll - (g - 1) = lh + ll - g by ring]
    exact herr'
  · rw [hlmv]; have := abs_le.mp herr'; have := abs_le.mp hll; linarith
  · rw [hlmv]; have := abs_le.mp herr'; have := abs_le.mp hll; linarith

theorem x1_le_1015 : (x1 : ℝ) ≤ 2 ^ 1015 := by
  have : x1 ≤ 2 ^ 1015 := by decide +kernel
  exact_mod_cast this

/-- **The leaf below `va`**, without the normalization. -/
theorem leaf_low (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hSF : LgammaApprox.StirlingFact) (ax : Float) (hax : Finite ax.toBits)
    (h800 : 2 ^ 800 ≤ value ax.toBits) (hva : value ax.toBits ≤ va) (L0 M N R : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable ax)
    (hM : M = ((mulDDD ax (L0.1 - 1.0) L0.2).1,
      (mulDDD ax (L0.1 - 1.0) L0.2).2 - (L0.1 - 1.0) * 0.5))
    (hN : N = fastSum M.1 M.2 (entry Lgamma.mainTable 397) (entry Lgamma.mainTable 398))
    (hR : R = fastSum N.1 N.2 0.0 0.0) :
    LeafTop (value ax.toBits) (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68) := by
  have hvx1 : value ax.toBits ≤ x1 := hva.trans (by exact_mod_cast va_le_x1)
  obtain ⟨hp1, hp2, hP, hp2b, hp1lo, hp1hi, hgx⟩ := logd_pair hF hL ax hax h800 hvx1 L0 hL0
  set v := value ax.toBits with hvdef
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) h800
  set g := Real.log v with hgdef
  have hg704 : g ≤ 704 := by
    have : (logX1Hi : ℝ) ≤ 704 := by
      have : logX1Hi ≤ 704 := by decide +kernel
      exact_mod_cast this
    linarith
  have hc0 : 0 ≤ g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21 := by
    have := abs_le.mp hP; have := abs_le.mp hp2b; linarith
  have hH : value (L0.1 - 1.0).toBits * v ≤ v * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) := by
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hv0.le
    have := abs_le.mp hP; have := abs_le.mp hp2b; linarith
  have hprod := products_ok.1
  have hprod' : ((va * (logX1Hi - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) : ℚ) : ℝ) ≤
      ((2 ^ 1024 - 13 * 2 ^ 968 : ℚ) : ℝ) := by exact_mod_cast hprod
  push_cast at hprod'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := stir_top_core hF hSF ax hax h800
    (hvx1.trans x1_le_1015) _ _ hp1 hp2 (hP.trans (by norm_num)) hp2b
    (v * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21)) hH
    (by nlinarith)
    (by
      have h1 : v * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) ≤
          (va : ℝ) * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) := mul_le_mul_of_nonneg_right hva hc0
      have h2 : (va : ℝ) * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) ≤
          (va : ℝ) * (logX1Hi - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 21) :=
        mul_le_mul_of_nonneg_left (by linarith) (by
          have : (0 : ℚ) ≤ va := by decide +kernel
          exact_mod_cast this)
      linarith)
    M N R hM hN hR
  exact leaf_stir_top v R hr1 hr2 hr3 hr4 hr5 hr6

/-- **The leaf from `va` to `x1`**, with the normalization. -/
theorem leaf_high (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hSF : LgammaApprox.StirlingFact) (ax : Float) (hax : Finite ax.toBits)
    (h800 : 2 ^ 800 ≤ value ax.toBits) (hx1 : value ax.toBits ≤ x1) (L0 P M N R : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable ax)
    (hP : P = fastTwoSum (L0.1 - 1.0) L0.2)
    (hM : M = ((mulDDD ax P.1 P.2).1, (mulDDD ax P.1 P.2).2 - P.1 * 0.5))
    (hN : N = fastSum M.1 M.2 (entry Lgamma.mainTable 397) (entry Lgamma.mainTable 398))
    (hR : R = fastSum N.1 N.2 0.0 0.0) :
    LeafTop (value ax.toBits) (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68) := by
  obtain ⟨hl1, hl2, hlP, hl2b, hl1lo, hl1hi, hgx⟩ := logd_pair hF hL ax hax h800 hx1 L0 hL0
  set v := value ax.toBits with hvdef
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) h800
  set g := Real.log v with hgdef
  have hg704 : g ≤ 704 := by
    have : (logX1Hi : ℝ) ≤ 704 := by
      have : logX1Hi ≤ 704 := by decide +kernel
      exact_mod_cast this
    linarith
  have hxy : |value L0.2.toBits| ≤ |value (L0.1 - 1.0).toBits| := by
    rw [abs_of_pos (show (0 : ℝ) < value (L0.1 - 1.0).toBits by linarith)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 ≤ 550)]
  have hlim : |value (L0.1 - 1.0).toBits| < 2 ^ 900 := by
    rw [abs_of_pos (by linarith)]; linarith [(by norm_num : (705 : ℝ) < 2 ^ 900)]
  obtain ⟨hp1, hp2, hsum, -, -⟩ := fastTwoSum_spec (L0.1 - 1.0) L0.2 hl1 hl2 hxy hlim
  have hhalf := Library.Numerics.Float64.Tgamma.TgammaDDTop.fts_half (L0.1 - 1.0) L0.2 hl1 hl2 hxy hlim
    (by have := abs_le.mp hl2b; linarith) (by have := abs_le.mp hl2b; linarith)
  rw [← hP] at hp1 hp2 hsum hhalf
  have hPv : |value P.1.toBits + value P.2.toBits - (g - 1)| ≤ 1 / 2 ^ 66 := by
    rw [hsum]; exact hlP.trans (by norm_num)
  have hc0 : 0 ≤ g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44 := by
    have := abs_le.mp hlP; have := abs_le.mp hl2b; linarith
  have hH : value P.1.toBits * v ≤ v * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) := by
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hv0.le
    have := abs_le.mp hPv; have := abs_le.mp hhalf; linarith
  have hprod := products_ok.2
  have hprod' : ((x1 * (logX1Hi - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) : ℚ) : ℝ) ≤
      ((2 ^ 1024 - 13 * 2 ^ 968 : ℚ) : ℝ) := by exact_mod_cast hprod
  push_cast at hprod'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := stir_top_core hF hSF ax hax h800
    (hx1.trans x1_le_1015) P.1 P.2 hp1 hp2 hPv (hhalf.trans (by norm_num))
    (v * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44)) hH
    (by nlinarith)
    (by
      have h1 : v * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) ≤
          (x1 : ℝ) * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) := mul_le_mul_of_nonneg_right hx1 hc0
      have h2 : (x1 : ℝ) * (g - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) ≤
          (x1 : ℝ) * (logX1Hi - 1 + 1 / 2 ^ 66 + 1 / 2 ^ 44) :=
        mul_le_mul_of_nonneg_left (by linarith) (by
          have : (0 : ℚ) ≤ x1 := by decide +kernel
          exact_mod_cast this)
      linarith)
    M N R hM hN hR
  exact leaf_stir_top v R hr1 hr2 hr3 hr4 hr5 hr6

/-- **The code's choice from `2^800` to `x1`**: when the rounding test passes, the fast result lies
within one step of `L` by its relative error, which `F64RelativeStep.within_one_relative` takes up
to the threshold; otherwise the accurate path does. -/
theorem top_within (fh fl eps sign acc : Float) (a : ℝ) (ht : LeafTop a (fh, fl, eps))
    (hLmax : GammaBasic.lgamma a ≤ 2 ^ 1024 - 5 * 2 ^ 969)
    (hacc : F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma a) acc.toBits) :
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma a)
      (if (fh + (fl + eps) != fh + (fl - eps)) = true then (acc, sign)
        else (fh + (fl + eps), sign)).1.toBits := by
  by_cases h : (fh + (fl + eps) != fh + (fl - eps)) = true
  · rw [ite_eq_left h]; exact hacc
  rw [ite_eq_right h]
  obtain ⟨h1, h2, h3, h8, hfmax, hflr, helo, hehi, hmain⟩ := ht
  simp only [] at h1 h2 h3 h8 hfmax hflr helo hehi hmain
  set L := GammaBasic.lgamma a with hLdef
  set f := value fh.toBits with hfdef
  set l := value fl.toBits with hldef
  set e := value eps.toBits with hedef
  have he0 : 0 ≤ e := by nlinarith
  have hfl : |l| ≤ f / 2 ^ 17 := hflr
  have hLf : |L - (f + l)| ≤ 2 * e := by
    have : 0 ≤ f / 2 ^ 67 := by positivity
    linarith
  have hLlo : 7 ≤ L := by
    have := abs_le.mp hLf; have := abs_le.mp hfl
    have : e ≤ 8 / 2 ^ 62 + f / 2 ^ 62 := by linarith
    nlinarith
  have hfL : f ≤ L * (1 + 1 / 2 ^ 15) := by
    have := abs_le.mp hLf; have := abs_le.mp hfl
    nlinarith
  have hs := fapprox_add (fapprox_self fl h2) (fapprox_self eps h3) (|l| + e) (by
      simp only [add_zero]
      have := abs_add_le l e
      rw [abs_of_nonneg he0] at this
      linarith) (by
      have : |l| + e ≤ (2 ^ 1024 - 2 ^ 971) / 2 ^ 17 + (2 ^ 1024 - 2 ^ 971) / 2 ^ 62 := by
        have a1 : f / 2 ^ 17 ≤ (2 ^ 1024 - 2 ^ 971) / 2 ^ 17 :=
          div_le_div_of_nonneg_right hfmax (by norm_num)
        have a2 : f / 2 ^ 62 ≤ (2 ^ 1024 - 2 ^ 971) / 2 ^ 62 :=
          div_le_div_of_nonneg_right hfmax (by norm_num)
        linarith
      linarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 971) / 2 ^ 17 + (2 ^ 1024 - 2 ^ 971) / 2 ^ 62
        < 2 ^ 1023)])
  have hse : |value (fl + eps).toBits - (l + e)| ≤ (|l| + e) / 2 ^ 53 := by
    have := hs.2
    simp only [zero_add] at this
    exact this
  set S := f + value (fl + eps).toBits with hSdef
  have hSL : |S - L| ≤ L / 2 ^ 58 := by
    have hd : S - L = (value (fl + eps).toBits - (l + e)) + e - (L - (f + l)) := by
      rw [hSdef]; ring
    rw [hd]
    have k1 := abs_sub (value (fl + eps).toBits - (l + e) + e) (L - (f + l))
    have k2 := abs_add_le (value (fl + eps).toBits - (l + e)) e
    rw [abs_of_nonneg he0] at k2
    have k3 : (|l| + e) / 2 ^ 53 ≤ (f / 2 ^ 17 + f / 2 ^ 62) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have k5 : f / 2 ^ 60 ≤ L * (1 + 1 / 2 ^ 15) / 2 ^ 60 :=
      div_le_div_of_nonneg_right hfL (by norm_num)
    linarith
  have hS0 : 0 < S := by
    have := abs_le.mp hSL
    linarith
  have hSmax : |S| < 2 ^ 1024 - 2 ^ 970 := by
    have := abs_le.mp hSL
    rw [abs_of_pos hS0]
    have : L / 2 ^ 58 ≤ (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 58 :=
      div_le_div_of_nonneg_right hLmax (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 1024 - 5 * 2 ^ 969 + (2 ^ 1024 - 5 * 2 ^ 969) / 2 ^ 58 <
      2 ^ 1024 - 2 ^ 970)]
  have hr := F64TopPack.add_real_relative_top fh.toBits (fl + eps).toBits h1 hs.1 hSmax
  rw [← F64Bits.toBits_add] at hr
  obtain ⟨hwf, hw⟩ := hr
  apply F64RelativeStep.within_one_relative _ _ hwf
  · rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 7)]
  · have hu : unitRoundoff64 = 1 / 2 ^ 53 := by norm_num [unitRoundoff64]
    rw [hu] at hw ⊢
    rw [abs_of_pos (show (0 : ℝ) < L by linarith)]
    have := abs_le.mp hSL
    rw [abs_of_pos hS0] at hw
    have k := abs_sub_le (value (fh + (fl + eps)).toBits) S L
    have k6 : |S - L| = |L - S| := abs_sub_comm S L
    linarith

/-- `LeafTop` on the first three parts of the fast path's block. -/
def TopEnd (a : ℝ) (r : Float × Float × Float × Float) : Prop :=
  LeafTop a (r.1, r.2.1, r.2.2.1)

theorem select_top (fh fl eps sign acc : Float) (a : ℝ) (h : TopEnd a (fh, fl, eps, sign))
    (hLmax : GammaBasic.lgamma a ≤ 2 ^ 1024 - 5 * 2 ^ 969)
    (hacc : F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma a) acc.toBits) :
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma a)
      (if (fh + (fl + eps) != fh + (fl - eps)) = true then (acc, sign)
        else (fh + (fl + eps), sign)).1.toBits :=
  top_within fh fl eps sign acc a h hLmax hacc

/-- `ln Γ` stays below `2^1024 - 5 · 2^969` up to `x1`. -/
theorem lgamma_le_top (v : ℝ) (h2 : 2 ≤ v) (hv : v ≤ x1) :
    GammaBasic.lgamma v ≤ 2 ^ 1024 - 5 * 2 ^ 969 := by
  have h1 := lgamma_mono h2 hv
  have h2 := (abs_le.mp lgamma_x1).2
  linarith [(by norm_num : (2 : ℝ) ^ 1024 - 2 ^ 972 + 3 / 5 * 2 ^ 971 ≤ 2 ^ 1024 - 5 * 2 ^ 969)]

open Lgamma LgammaBranches LgammaWalk LgammaLeaf LgammaFastWalk in
open Library.Numerics.Float64.Tgamma (floorF) in
set_option maxHeartbeats 4000000 in
/-- **One step for the code's choice from `2^800` to `x1`**, when the accurate path is within one
step. -/
theorem fast_top (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hSF : LgammaApprox.StirlingFact) (x : Float) (hx : Finite x.toBits)
    (h800 : 2 ^ 800 ≤ value x.toBits) (hx1 : x.toBits.toNat < 0x7F5754D9278B51A6)
    (hacc : F64SignedRounding.WithinSteps 1 (Real.log (Real.Gamma (value x.toBits)))
      (Lgamma.accurate Tgamma.logdTable Lgamma.logAccurateTable Lgamma.sinpiTable
        Lgamma.asymTable Lgamma.accurateTable Lgamma.dbTable x).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.log (Real.Gamma (value x.toBits)))
      (Lgamma.lgammaR x).1.toBits := by
  have hpos : 0 < value x.toBits := lt_of_lt_of_le (by positivity) h800
  have hx63 : x.toBits.toNat < 2 ^ 63 := by
    have hs := F64Exact.sign_of_pos x.toBits hpos
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hvx1 : value x.toBits ≤ (x1 : ℝ) := by
    rw [← x1_word, PolyBound.ratOfWord_cast]
    exact (F64PositiveOrder.value_le_iff hx63 (by decide)).mpr (by
      simp only [UInt64.reduceToNat]; omega)
  have h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C := fun h => by
    have := (LgammaSpecial.big_test _).mp h; omega
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float x hx
  have hfb := fin_bits _ hx
  have habsN : (x.abs.toBits).toNat = x.toBits.toNat % 9223372036854775808 := by
    rw [F64Bits.toBits_abs, F64UpperWord.abs_toNat]; rfl
  have hsignf : ¬ (x.toBits >>> 63 == 1) = true := by
    intro hn
    have := (LgammaSpecial.sign_test _).mp hn
    omega
  have h2 : ¬ (floorF x == x && x ≤ 0.0) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff,
      LgammaSpecial.float_le_iff _ _ hx LgammaSpecial.zero_finite, Library.Numerics.Float64.Tgamma.TgammaSpecial.zero_bits,
      F64Magnitude.value_zero]
    rintro ⟨-, hle⟩
    linarith
  have h3 : ¬ (floorF x == x && (x == 1.0 || x == 2.0)) = true := by
    rw [Bool.and_eq_true, Bool.or_eq_true, F64UpperWord.float_beq_iff _ _ hx LgammaSpecial.one_finite,
      F64UpperWord.float_beq_iff _ _ hx LgammaSpecial.two_finite, LgammaSpecial.one_value,
      LgammaSpecial.two_value]
    rintro ⟨-, h | h⟩ <;> rw [h] at h800 <;> norm_num at h800
  have hLmax : Real.log (Real.Gamma (value x.toBits)) ≤ 2 ^ 1024 - 5 * 2 ^ 969 :=
    lgamma_le_top _ (by linarith [(by norm_num : (2 : ℝ) ≤ 2 ^ 800)]) hvx1
  unfold Lgamma.lgammaR
  rewrite [lgammaWith.eq_1, ite_eq_right h1]
  extract_lets fx au sgn z z2 z4 q0 q2 q4 q6 ax zh zl z2h z4h q0s q2s fls j0 z0
  have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
  have h3' : ¬ (fx == x && (x == 1.0 || x == 2.0)) = true := h3
  rewrite [ite_eq_right h2', ite_eq_right h3']
  split
  next fh fl eps sign heq =>
  extract_lets ub lb
  refine select_top fh fl eps sign _ (value x.toBits) ?_ hLmax hacc
  rw [← heq]
  clear heq
  have hauN : au.toNat = x.toBits.toNat % 9223372036854775808 / 137438953472 := au_nat x.toBits
  have hx2 : 2 ^ 800 ≤ |value x.toBits| := by rw [abs_of_pos hpos]; exact h800
  have hxw : 0x71F0000000000000 ≤ x.toBits.toNat := by
    by_contra hc
    push Not at hc
    have := abs_lt_word x.toBits _ _ w800 (by decide)
      (by simp only [UInt64.reduceToNat]; omega)
    linarith
  walk_step
  · intro hc
    rw [LgammaPieceIdx.tab0, UInt64.lt_iff_toNat_lt] at hc
    simp only [UInt64.reduceToNat] at hc
    exfalso
    omega
  · intro hc
    have hax : value ax.toBits = |value x.toBits| := hav
    have hax' : value ax.toBits = value x.toBits := by rw [hax, abs_of_pos hpos]
    have haxN : ax.toBits.toNat / 137438953472 = au.toNat := by rw [hauN, ← habsN]
    walk_bridge (LeafTop (value ax.toBits))
    · walk_step
      · intro h19
        walk_step; intro lh ll hL0
        walk_step; intro lh1 hlh1
        subst hlh1
        walk_step; intro m1 m2 hM
        walk_step; intro n1 n2 hN
        walk_step; intro t1 t2 hT
        walk_step; intro r1 r2 hR
        have hbig : au ≥ 35225600 := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le]
          simp only [UInt64.reduceToNat]
          omega
        rw [ite_eq_left hbig] at hM
        have h100 : ¬ ax < Float.ofBits 5057542381537067008 := by
          rw [F64UpperWord.float_lt_iff _ _ haf w100_finite, w100, hax']
          linarith [(by norm_num : (2 : ℝ) ^ 100 ≤ 2 ^ 800)]
        rw [ite_eq_right h100] at hT
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hT
        have hv800 : 2 ^ 800 ≤ value ax.toBits := by rw [hax']; exact h800
        by_cases htop : au ≥ 66763430
        · rw [ite_eq_left htop] at hM
          dsimp only at hM
          obtain ⟨q1, q2, hq⟩ : ∃ q1 q2, Tgamma.fastTwoSum (lh - 1.0) ll = (q1, q2) := ⟨_, _, rfl⟩
          rw [hq] at hM
          dsimp only at hM
          obtain ⟨d1, d2, hd⟩ : ∃ d1 d2, Tgamma.mulDDD ax q1 q2 = (d1, d2) := ⟨_, _, rfl⟩
          rw [hd] at hM
          dsimp only at hM
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hM
          exact leaf_high hF hL hSF ax haf hv800 (by rw [hax']; exact hvx1) (lh, ll) (q1, q2)
            (d1, d2 - q1 * 0.5) (n1, n2) (r1, r2) hL0.symm hq.symm (by rw [hd]) hN.symm hR.symm
        · rw [ite_eq_right htop] at hM
          dsimp only at hM
          obtain ⟨d1, d2, hd⟩ : ∃ d1 d2, Tgamma.mulDDD ax (lh - 1.0) ll = (d1, d2) :=
            ⟨_, _, rfl⟩
          rw [hd] at hM
          dsimp only at hM
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hM
          have hva : value ax.toBits ≤ va := by
            rw [ge_iff_le, UInt64.le_iff_toNat_le, not_le] at htop
            simp only [UInt64.reduceToNat] at htop
            have hw : value (0x7F5754C000000000 : UInt64) = (va : ℝ) := by
              rw [← PolyBound.ratOfWord_cast]
              congr 1
              decide +kernel
            rw [← hw, hax']
            exact (F64PositiveOrder.value_le_iff hx63 (by decide)).mpr (by
              simp only [UInt64.reduceToNat]; omega)
          exact leaf_low hF hL hSF ax haf hv800 hva (lh, ll) (d1, d2 - (lh - 1.0) * 0.5)
            (n1, n2) (r1, r2) hL0.symm (by rw [hd]) hN.symm hR.symm
      · intro h19
        rw [tab19, ge_iff_le, UInt64.le_iff_toNat_le, not_le] at h19
        simp only [UInt64.reduceToNat] at h19
        exfalso
        omega
    · intro fh fl eps hl
      walk_step
      · intro hn
        exact absurd hn hsignf
      · intro _
        rw [hax'] at hl
        exact hl

#print axioms log_x1_le
#print axioms products_ok
#print axioms logd_pair
#print axioms leaf_low
#print axioms leaf_high
#print axioms top_within
#print axioms fast_top

end Library.Numerics.Float64.Lgamma.LgammaFastTop
