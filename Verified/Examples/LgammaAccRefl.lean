import Verified.Examples.LgammaAccWinSmall
import Verified.Examples.LgammaSinAcc
import Verified.Examples.LgammaReflMid

/-!
The reflection of `Lgamma.accurate` at a negative argument `sx` from `-2^52` to `-1/4`.  The code
computes `log Γ (1 + |sx|)` as a triple, `φ = sx - ⌊sx⌋` below `-1/2` and `-sx` above
(`phi_spec`), the accurate sine `sh + sl ≈ sin (π φ)/π` (`LgammaSinAcc.sinAcc_spec`), the logarithm
of `sh` with `sl/sh` added to its middle part (`slog_spec`, within `2^-84` of
`log (sin (π φ)/π)`), and the sum of the two by `addLog`, and it negates the result.  Since
`sin (π φ) = |sin (π sx)|`, `log Γ (1 - sx) + log |Γ sx| = log π - log |sin (π sx)|` gives
`log |Γ sx| = -(log Γ (1 + |sx|) + log (sin (π φ)/π))` (`refl_id`), and the result is within the
error of the triple plus `2^-84` (`refl_spec`).  The theorems take the intermediate results of
the code as variables with their equations.
-/

namespace Verified.Examples.LgammaAccRefl
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD LgammaLogAccKern LgammaAccLow
  LgammaAccAdd LgammaAccWin
open Verified.Examples.Tgamma (floorF)

set_option exponentiation.threshold 4096

/-- **The reflection identity** with `φ` such that `sin (π φ) = |sin (π v)|`. -/
theorem refl_id (v φ : ℝ) (hv : v < 0) (hint : ∀ n : ℤ, v ≠ n)
    (hφ : Real.sin (Real.pi * φ) = |Real.sin (Real.pi * v)|) :
    GammaBasic.lgamma v =
      -(GammaBasic.lgamma (1 + |v|) + Real.log (Real.sin (Real.pi * φ) / Real.pi)) := by
  have hr := GammaBasic.lgamma_reflect hint
  have hs := GammaBasic.sin_pi_ne_zero hint
  rw [abs_of_neg hv, show 1 + -v = 1 - v by ring,
    Real.log_div (by rw [hφ]; exact abs_ne_zero.mpr hs) Real.pi_ne_zero, hφ, Real.log_abs]
  linarith

theorem m05 : Finite (-0.5 : Float).toBits ∧ value (-0.5 : Float).toBits = -(1 / 2) := by
  obtain ⟨f, v⟩ := neg_float 0.5 c05.1
  exact ⟨f, by rw [v, c05.2]⟩

/-- **The argument of the sine**: `φ = n/2^54` with `sin (π φ) = |sin (π sx)|`. -/
theorem phi_spec (sx : Float) (hsx : Finite sx.toBits) (hneg : value sx.toBits < 0)
    (hint : ∀ n : ℤ, value sx.toBits ≠ n) (hq : value sx.toBits ≤ -1 / 4)
    (hbig : -2 ^ 52 < value sx.toBits) (phi : Float)
    (hphi : phi = if sx < -0.5 then sx - floorF sx else -sx) :
    Finite phi.toBits ∧ (∃ n : ℕ, 0 < n ∧ n < 2 ^ 54 ∧ value phi.toBits = n / 2 ^ 54) ∧
      Real.sin (Real.pi * value phi.toBits) = |Real.sin (Real.pi * value sx.toBits)| := by
  split_ifs at hphi with h
  · have hlt : value sx.toBits < -1 / 2 := by
      rw [F64UpperWord.float_lt_iff _ _ hsx m05.1, m05.2] at h; linarith
    obtain ⟨-, -, hdf, hdv, n, hn0, hn, hfn⟩ := LgammaReflCore.refl_frac sx hsx hbig hlt.le hint
    subst hphi
    refine ⟨hdf, ⟨2 * n, by omega, by have := hn; norm_num at this ⊢; omega,
      by rw [hdv, hfn]; push_cast; ring⟩, ?_⟩
    rw [hdv, GammaBasic.sin_pi_eq (value sx.toBits), abs_mul, abs_zpow, abs_neg, abs_one, one_zpow,
      one_mul, abs_of_pos (GammaBasic.sin_pi_fract_pos hint)]
  · have hge : -(1 / 2) ≤ value sx.toBits := by
      rw [F64UpperWord.float_lt_iff _ _ hsx m05.1, m05.2] at h; push_neg at h; exact h
    obtain ⟨nf, nv⟩ := neg_float sx hsx
    subst hphi
    obtain ⟨z, hz⟩ := TgammaAccPre.grid54 (-sx) nf (by rw [nv, abs_neg, abs_of_neg hneg]; linarith)
    rw [nv] at hz
    have hz1 : (2 : ℝ) ^ 52 ≤ z := by
      have : (z : ℝ) = -value sx.toBits * 2 ^ 54 := by rw [hz]; field_simp
      rw [this]; nlinarith
    have hz2 : (z : ℝ) ≤ 2 ^ 53 := by
      have : (z : ℝ) = -value sx.toBits * 2 ^ 54 := by rw [hz]; field_simp
      rw [this]; nlinarith
    have hz0 : 0 ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by linarith)
    refine ⟨nf, ⟨z.toNat, ?_, ?_, ?_⟩, ?_⟩
    · have : (2 : ℤ) ^ 52 ≤ z := by exact_mod_cast hz1
      norm_num at this ⊢; omega
    · have : z ≤ (2 : ℤ) ^ 53 := by exact_mod_cast hz2
      norm_num at this ⊢; omega
    · rw [nv, hz]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg hz0).symm
    · rw [nv, mul_neg, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, Real.pi_gt_three]))]

set_option maxHeartbeats 4000000 in
/-- **The logarithm of the accurate sine**, with `sl/sh` added to its middle part, within `2^-84`
of `log (sin (π φ)/π)`. -/
theorem slog_spec (hF : FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact)
    (hSA : LgammaApprox.SinpiAccFact) (hLA : LgammaApprox.LogAccFact) (phi : Float)
    (hphi : Finite phi.toBits) (n : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ 54)
    (hv : value phi.toBits = n / 2 ^ 54)
    (sh sl : Float) (hA : Lgamma.asSinpipidAccurate Lgamma.sinpiTable phi = (sh, sl))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H sh = (lh, ll, lll)) :
    Finite lh.toBits ∧ Finite (ll + (sl / sh + lll)).toBits ∧
      |value lh.toBits + value (ll + (sl / sh + lll)).toBits -
          Real.log (Real.sin (Real.pi * value phi.toBits) / Real.pi)| ≤ 1 / 2 ^ 84 ∧
      |value lh.toBits| ≤ 40 ∧ |value (ll + (sl / sh + lll)).toBits| ≤ 1 / 2 ^ 40 := by
  obtain ⟨f1, f2, he, hl⟩ := LgammaSinAcc.sinAcc_spec hF hS hSA phi n hn0 hn hphi hv
  rw [hA] at f1 f2 he hl
  dsimp only at f1 f2 he hl
  set φ := value phi.toBits with hφ
  set s := Real.sin (Real.pi * φ) / Real.pi with hsdef
  have hφ0 : 1 / 2 ^ 54 ≤ φ := by
    rw [hv]; exact div_le_div_of_nonneg_right (by exact_mod_cast hn0) (by positivity)
  have hφ1 : φ ≤ 1 - 1 / 2 ^ 54 := by
    rw [hv]
    have : (n : ℝ) + 1 ≤ 2 ^ 54 := by exact_mod_cast hn
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsJ := LgammaReflMid.s_jordan φ (by linarith) (by linarith)
  rw [← hsdef] at hsJ
  have hs0 : 1 / 2 ^ 55 ≤ s := by
    have : 1 / 2 ^ 54 ≤ 1 / 2 - |φ - 1 / 2| := by
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', abs_le]; constructor <;> linarith
    linarith
  have hs1 : s ≤ 1 / 3 := by
    rw [hsdef, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    have := Real.sin_le_one (Real.pi * φ)
    have := Real.pi_gt_three
    linarith
  set a := value sh.toBits
  set b := value sl.toBits
  -- `sh` from `s`
  have hsum_lo : s * (1 - 1 / 2 ^ 85) ≤ a + b := by have := (abs_le.mp he).1; linarith
  have hsum_hi : a + b ≤ s * (1 + 1 / 2 ^ 85) := by have := (abs_le.mp he).2; linarith
  have ha0 : 0 < a := by
    by_contra h
    push_neg at h
    rw [abs_of_nonpos h] at hl
    have := (abs_le.mp hl).2
    nlinarith
  rw [abs_of_pos ha0] at hl
  have hb := abs_le.mp hl
  have halo : 1 / 2 ^ 56 ≤ a := by nlinarith
  have hahi : a ≤ 1 / 2 := by nlinarith
  -- the logarithm of `sh`
  obtain ⟨t1f, t2f, t3f, te, t2b, t3b⟩ := LgammaLogdAcc.acc_abs hF hLA sh f1 ha0
  rw [hT] at t1f t2f t3f te t2b t3b
  dsimp only at t1f t2f t3f te t2b t3b
  have hla_hi : Real.log a < 0 := Real.log_neg ha0 (by linarith)
  have hla_lo : -(3882 / 100) ≤ Real.log a := by
    have h := Real.log_le_log (by positivity) halo
    rw [one_div, Real.log_inv, Real.log_pow] at h
    have := Real.log_two_lt_d9
    push_cast at h
    linarith
  set l0 := value lh.toBits
  set l1 := value ll.toBits
  set l2 := value lll.toBits
  have hl0 : |l0| ≤ 39 := by
    have h3 : |l0| ≤ 3882 / 100 + 1 / 2 ^ 88 + |l1| + |l2| := by
      have := abs_add_le (l0 + l1 + l2 - Real.log a) (-(l1 + l2) + Real.log a)
      have h4 := abs_add_le (-(l1 + l2)) (Real.log a)
      have h5 := abs_add_le l1 l2
      rw [show l0 + l1 + l2 - Real.log a + (-(l1 + l2) + Real.log a) = l0 by ring] at this
      rw [abs_neg, abs_of_neg hla_hi] at h4
      linarith
    linarith
  have hl1 : |l1| ≤ 1 / 2 ^ 45 := by
    have := div_le_div_of_nonneg_right hl0 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    linarith [(by norm_num : (39 : ℝ) / 2 ^ 51 + 1 / 2 ^ 50 ≤ 1 / 2 ^ 45)]
  have hl2 : |l2| ≤ 1 / 2 ^ 94 := by
    have := div_le_div_of_nonneg_right hl0 (by norm_num : (0 : ℝ) ≤ 2 ^ 100)
    linarith [(by norm_num : (39 : ℝ) / 2 ^ 100 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 94)]
  -- `sl / sh`, `+ lll`, `ll +`
  have hba : |b / a| ≤ 1 / 2 ^ 47 := by
    rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]; linarith [abs_le.mpr hb]
  have hq := fapprox_div (fapprox_self sl f2) (fapprox_self sh f1) |b| a le_rfl
    (by rw [abs_of_pos ha0]) (by linarith) (1 / 2 ^ 47)
    (by rw [add_zero, sub_zero, div_le_iff₀ ha0]; linarith [abs_le.mpr hb]) (by norm_num)
  simp only [zero_add, mul_zero, zero_div, sub_zero] at hq
  have hr := fapprox_add hq (fapprox_self lll t3f) (1 / 2 ^ 46) (by
    have := abs_add_le (b / a) l2
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 47 + 1 / 2 ^ 94 + (1 / 2 ^ 47 / 2 ^ 53 + 1 / 2 ^ 1075 + 0)
      ≤ 1 / 2 ^ 46)]) (by norm_num)
  have hr2 := fapprox_add (fapprox_self ll t2f) hr (1 / 2 ^ 44) (by
    have := abs_add_le l1 (b / a + l2)
    have := abs_add_le (b / a) l2
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 45 + (1 / 2 ^ 47 + 1 / 2 ^ 94) +
      (0 + (1 / 2 ^ 47 / 2 ^ 53 + 1 / 2 ^ 1075 + 0 + 1 / 2 ^ 46 / 2 ^ 53)) ≤ 1 / 2 ^ 44)])
    (by norm_num)
  obtain ⟨hf2, he2⟩ := hr2
  have he2' : |value (ll + (sl / sh + lll)).toBits - (l1 + (b / a + l2))| ≤ 1 / 2 ^ 96 := by
    linarith [(by norm_num : (0 : ℝ) + (1 / 2 ^ 47 / 2 ^ 53 + 1 / 2 ^ 1075 + 0 + 1 / 2 ^ 46 / 2 ^ 53) +
      1 / 2 ^ 44 / 2 ^ 53 ≤ 1 / 2 ^ 96)]
  -- the logarithms
  have hlog1 : |b / a - Real.log (1 + b / a)| ≤ 1 / 2 ^ 91 := by
    rw [abs_sub_comm]; exact TgammaAsym3.log_one_add _ (hba.trans (by norm_num))
  have hab : Real.log (a + b) = Real.log a + Real.log (1 + b / a) := by
    rw [← Real.log_mul ha0.ne' (ne_of_gt (by
      have := abs_le.mp hba; linarith [(by norm_num : (1 : ℝ) / 2 ^ 47 < 1)]))]
    congr 1
    rw [mul_add, mul_one, mul_div_assoc', mul_div_cancel_left₀ b ha0.ne']
  have hs_pos : 0 < s := by linarith
  have hlog2 : |Real.log (a + b) - Real.log s| ≤ 1 / 2 ^ 84 - 1 / 2 ^ 86 := by
    have hq' : (a + b) / s = 1 + ((a + b) / s - 1) := by ring
    have hδ : |(a + b) / s - 1| ≤ 1 / 2 ^ 85 := by
      rw [abs_le]; constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hs_pos]; nlinarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hs_pos]; nlinarith
    have hl := LgammaReflCore.abs_log_one_add _ (hδ.trans (by norm_num))
    rw [← hq', Real.log_div (ne_of_gt (by linarith)) hs_pos.ne'] at hl
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 85 + 1 / 2 ^ 91 ≤ 1 / 2 ^ 84 - 1 / 2 ^ 86)]
  refine ⟨t1f, hf2, ?_, hl0.trans (by norm_num), ?_⟩
  · have k : l0 + value (ll + (sl / sh + lll)).toBits - Real.log s =
        (l0 + l1 + l2 - Real.log a) + (value (ll + (sl / sh + lll)).toBits - (l1 + (b / a + l2))) +
          (b / a - Real.log (1 + b / a)) + (Real.log (a + b) - Real.log s) := by
      rw [hab]; ring
    rw [k]
    have e1 := abs_add_le ((l0 + l1 + l2 - Real.log a) +
      (value (ll + (sl / sh + lll)).toBits - (l1 + (b / a + l2))) + (b / a - Real.log (1 + b / a)))
      (Real.log (a + b) - Real.log s)
    have e2 := abs_add_le ((l0 + l1 + l2 - Real.log a) +
      (value (ll + (sl / sh + lll)).toBits - (l1 + (b / a + l2)))) (b / a - Real.log (1 + b / a))
    have e3 := abs_add_le (l0 + l1 + l2 - Real.log a)
      (value (ll + (sl / sh + lll)).toBits - (l1 + (b / a + l2)))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 96 + 1 / 2 ^ 91 ≤ 1 / 2 ^ 86)]
  · have := abs_sub_abs_le_abs_sub (value (ll + (sl / sh + lll)).toBits) (l1 + (b / a + l2))
    have := abs_add_le l1 (b / a + l2)
    have := abs_add_le (b / a) l2
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 96 + 1 / 2 ^ 45 + 1 / 2 ^ 47 + 1 / 2 ^ 94 ≤ 1 / 2 ^ 40)]

set_option maxHeartbeats 4000000 in
/-- **The reflection**: the negated sum of the triple of `log Γ (1 + |sx|)` and the logarithm of
the accurate sine is within the triple's error plus `2^-84` and `addLog`'s error of
`log |Γ sx|`, with the values of the negated parts. -/
theorem refl_spec (hF : FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact)
    (hSA : LgammaApprox.SinpiAccFact) (hLA : LgammaApprox.LogAccFact) (sx : Float)
    (hsx : Finite sx.toBits) (hneg : value sx.toBits < 0) (hint : ∀ n : ℤ, value sx.toBits ≠ n)
    (hq : value sx.toBits ≤ -1 / 4) (hbig : -2 ^ 52 < value sx.toBits)
    (fh fl fll : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits)
    (hfll : Finite fll.toBits) (E Bl Bll : ℝ)
    (hE : |value fh.toBits + value fl.toBits + value fll.toBits -
      GammaBasic.lgamma (1 + |value sx.toBits|)| ≤ E)
    (hfhb : |value fh.toBits| ≤ 2 ^ 840) (hflb : |value fl.toBits| ≤ Bl) (hBl : Bl ≤ 2 ^ 830)
    (hfllb : |value fll.toBits| ≤ Bll) (hBll : Bll ≤ 2 ^ 780)
    (phi : Float) (hphi : phi = if sx < -0.5 then sx - floorF sx else -sx)
    (sh sl : Float) (hA : Lgamma.asSinpipidAccurate Lgamma.sinpiTable phi = (sh, sl))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H sh = (lh, ll, lll))
    (ll2 : Float) (hll2 : ll2 = ll + (sl / sh + lll))
    (a1 b1 : Float) (hS1 : sumDD fl fll ll2 0.0 = (a1, b1))
    (h2 l2 : Float) (hP2 : twoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    Finite (-h2).toBits ∧ Finite (-a3).toBits ∧ Finite (-b3).toBits ∧
      value (-h2).toBits = -value h2.toBits ∧ value (-a3).toBits = -value a3.toBits ∧
      value (-b3).toBits = -value b3.toBits ∧
      |value (-h2).toBits + value (-a3).toBits + value (-b3).toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        E + 1 / 2 ^ 84 + ((7 * Bll + (Bl + 1 / 2 ^ 40) / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) /
          2 ^ 53 + 1 / 2 ^ 1100) ∧
      |value h2.toBits| ≤ (|value fh.toBits| + 40) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value a3.toBits| ≤ (Bl + 1 / 2 ^ 40 + |value h2.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) +
        1 / 2 ^ 1070 ∧
      |value b3.toBits| ≤ (Bll + (Bl + 1 / 2 ^ 40) / 2 ^ 50) * (1 + 1 / 2 ^ 49) +
        |value a3.toBits| / 2 ^ 51 + 1 / 2 ^ 1070 := by
  obtain ⟨pf, ⟨n, hn0, hn, hpv⟩, hsin⟩ := phi_spec sx hsx hneg hint hq hbig phi hphi
  obtain ⟨lf, l2f, le, lb, l2b⟩ := slog_spec hF hS hSA hLA phi pf n hn0 hn hpv sh sl hA lh ll lll hT
  rw [← hll2] at l2f le l2b
  have hid := refl_id (value sx.toBits) (value phi.toBits) hneg hint hsin
  have hBl0 : 0 ≤ Bl := le_trans (abs_nonneg _) hflb
  have hBll0 : 0 ≤ Bll := le_trans (abs_nonneg _) hfllb
  obtain ⟨f2, f3, f4, herr, hh2, ha3, hb3⟩ := addLog_wide fh fl fll lh ll2 0.0 hfh hfl hfll lf l2f
    zero_finite (|value fh.toBits| + 40) (Bl + 1 / 2 ^ 40) Bll (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 840 + 40 ≤ 2 ^ 850)]) (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 830 + 1 / 2 ^ 40 ≤ 2 ^ 840)])
    (by rw [zero_value, abs_zero, add_zero]; exact hfllb) (hBll.trans (by norm_num))
    a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
  rw [zero_value, add_zero] at herr
  obtain ⟨n2f, n2v⟩ := neg_float h2 f2
  obtain ⟨n3f, n3v⟩ := neg_float a3 f3
  obtain ⟨n4f, n4v⟩ := neg_float b3 f4
  refine ⟨n2f, n3f, n4f, n2v, n3v, n4v, ?_, ?_, ha3, hb3⟩
  · rw [n2v, n3v, n4v, hid]
    have k : -value h2.toBits + -value a3.toBits + -value b3.toBits -
        -(GammaBasic.lgamma (1 + |value sx.toBits|) +
          Real.log (Real.sin (Real.pi * value phi.toBits) / Real.pi)) =
        -((value h2.toBits + value a3.toBits + value b3.toBits -
            (value fh.toBits + value fl.toBits + value fll.toBits +
              (value lh.toBits + value ll2.toBits))) +
          (value fh.toBits + value fl.toBits + value fll.toBits -
            GammaBasic.lgamma (1 + |value sx.toBits|)) +
          (value lh.toBits + value ll2.toBits -
            Real.log (Real.sin (Real.pi * value phi.toBits) / Real.pi))) := by ring
    rw [k, abs_neg]
    have e1 := abs_add_le ((value h2.toBits + value a3.toBits + value b3.toBits -
            (value fh.toBits + value fl.toBits + value fll.toBits +
              (value lh.toBits + value ll2.toBits))) +
          (value fh.toBits + value fl.toBits + value fll.toBits -
            GammaBasic.lgamma (1 + |value sx.toBits|)))
        (value lh.toBits + value ll2.toBits -
            Real.log (Real.sin (Real.pi * value phi.toBits) / Real.pi))
    have e2 := abs_add_le (value h2.toBits + value a3.toBits + value b3.toBits -
            (value fh.toBits + value fl.toBits + value fll.toBits +
              (value lh.toBits + value ll2.toBits)))
          (value fh.toBits + value fl.toBits + value fll.toBits -
            GammaBasic.lgamma (1 + |value sx.toBits|))
    linarith
  · have h1 := abs_add_le (value fh.toBits) (value lh.toBits)
    have h3 := mul_le_mul_of_nonneg_right (h1.trans (by linarith : |value fh.toBits| +
      |value lh.toBits| ≤ |value fh.toBits| + 40)) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith

#print axioms refl_spec

#print axioms refl_id
#print axioms phi_spec
#print axioms slog_spec

end Verified.Examples.LgammaAccRefl
