import Verified.Examples.LgammaWalk
import Verified.Examples.LgammaLogd
import Verified.Examples.SinpiTiny
import Verified.Examples.SinhWords
import Verified.Examples.TgammaWords

/-!
The fast path of `Lgamma.lgammaWith` below `2 ^ -75` in magnitude, where the code returns
`-log |x|` from `asLogd` with the error bound `eps = 1.5 · 10 ^ -22`.  There
`|lgamma x + log |x|| ≤ 4 |x| ≤ 2 ^ -73` (`GammaBasic.abs_lgamma_add_log_le`), `asLogd` is within
`2 ^ -69 + |log |x||/2 ^ 78` of `log |x|`, and `|lgamma x| ≥ 50`, so the error with `2 eps` lies far
below `|lgamma x|/2 ^ 54` and `FastSpec` holds in its relative form (`tiny_spec`).
-/

namespace Verified.Examples.LgammaFastTiny
open CodeLib.IEEE64 LeanExe.ProofKit LgammaWalk PolyBound

set_option exponentiation.threshold 4096

/-- The negation of a finite double. -/
theorem neg_float (x : Float) (hx : Finite x.toBits) :
    Finite (-x).toBits ∧ value (-x).toBits = -value x.toBits := by
  have hb : (-x).toBits = Wasm.IEEE64.negate x.toBits := by
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite hx]
    rfl
  rw [hb]
  exact F64Magnitude.negate_value _ hx

/-- `|log |v||` for a nonzero double below `2 ^ -75` in magnitude. -/
theorem log_range (v : ℝ) (h0 : 1 / 2 ^ 1074 ≤ |v|) (h1 : |v| < 1 / 2 ^ 75) :
    51 ≤ -Real.log |v| ∧ -Real.log |v| ≤ 745 := by
  have hv : 0 < |v| := lt_of_lt_of_le (by positivity) h0
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9; linarith
  have hlo := Real.log_le_log (by positivity) h0
  have hhi := Real.log_lt_log hv h1
  rw [one_div, Real.log_inv, Real.log_pow] at hlo hhi
  push_cast at hlo hhi
  constructor <;> nlinarith

/-- **The fast path below `2 ^ -75`.** -/
theorem tiny_spec (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact) (x : Float)
    (hx : Finite x.toBits) (hx0 : value x.toBits ≠ 0) (htiny : |value x.toBits| < 1 / 2 ^ 75)
    (lh ll : Float) (h : Lgamma.asLogd Tgamma.logdTable x.abs = (lh, ll)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-lh, -ll, Float.ofBits 0x3B66AAD80C11872C, sign) := by
  set v := value x.toBits with hvdef
  obtain ⟨haf, hav⟩ := SinhWords.abs_float x hx
  have hpos : 0 < value x.abs.toBits := by rw [hav]; exact abs_pos.mpr hx0
  obtain ⟨hlf, hllf, herr, hllb⟩ := LgammaLogd.asLogd_spec hF hL x.abs haf hpos
  rw [h] at hlf hllf herr hllb
  dsimp only at hlf hllf herr hllb
  rw [hav] at herr
  obtain ⟨hnlf, hnlv⟩ := neg_float lh hlf
  obtain ⟨hnllf, hnllv⟩ := neg_float ll hllf
  have hcw : Wasm.IEEE64.isFinite 0x3B66AAD80C11872C = true := by decide
  have hcf : Finite (Float.ofBits 0x3B66AAD80C11872C).toBits := TgammaWords.ofBits_finite _ hcw
  have hcq : (1 / 2 ^ 73 : ℚ) ≤ ratOfWord 0x3B66AAD80C11872C ∧
      ratOfWord 0x3B66AAD80C11872C ≤ 1 / 2 ^ 72 := by decide +kernel
  have hcv : value (Float.ofBits 0x3B66AAD80C11872C).toBits =
      (ratOfWord 0x3B66AAD80C11872C : ℝ) := TgammaWords.ofBits_value _ hcw
  have hc1 : (1 / 2 ^ 73 : ℝ) ≤ value (Float.ofBits 0x3B66AAD80C11872C).toBits := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcq.1
    push_cast at h
    rw [hcv]; exact h
  have hc2 : value (Float.ofBits 0x3B66AAD80C11872C).toBits ≤ 1 / 2 ^ 72 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcq.2
    push_cast at h
    rw [hcv]; exact h
  -- `lgamma v` against `-log |v|`
  have hmin := SinpiTiny.abs_ge_min x.toBits hx0
  obtain ⟨hlg1, hlg2⟩ := log_range v hmin htiny
  have hgam := GammaBasic.abs_lgamma_add_log_le hx0
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 75 ≤ 1 / 4)])
  rw [GammaBasic.lgamma, ← Real.log_abs v] at hgam
  have hv73 : 4 * |v| ≤ 1 / 2 ^ 73 := by
    linarith [(by norm_num : (4 : ℝ) * (1 / 2 ^ 75) = 1 / 2 ^ 73)]
  set L := Real.log (Real.Gamma v) with hLdef
  set g := Real.log |v| with hgdef
  set a := value lh.toBits with hadef
  set b := value ll.toBits with hbdef
  have hgabs : |g| ≤ 745 := by rw [abs_le]; constructor <;> linarith
  have hgam' := abs_le.mp hgam
  have hL1 : 50 ≤ |L| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hL2 : |L| ≤ 746 := by
    rw [abs_le]; constructor <;> linarith
  -- the low part
  have hb21 : |b| ≤ 1 / 2 ^ 21 := by
    have h1 := abs_add_three (a + b - g) g (-b)
    rw [show a + b - g + g + -b = a by ring, abs_neg] at h1
    have h2 : |a| / 2 ^ 52 ≤ (|a + b - g| + |g| + |b|) / 2 ^ 52 :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : |g| / 2 ^ 78 ≤ 745 / 2 ^ 78 := div_le_div_of_nonneg_right hgabs (by positivity)
    linarith
  -- the error
  have hsum : |L - (-a + -b)| ≤ 1 / 2 ^ 73 + (1 / 2 ^ 69 + 745 / 2 ^ 78) := by
    have h1 := abs_add_le (L + g) (a + b - g)
    rw [show L + g + (a + b - g) = L - (-a + -b) by ring] at h1
    have h3 : |g| / 2 ^ 78 ≤ 745 / 2 ^ 78 := div_le_div_of_nonneg_right hgabs (by positivity)
    linarith
  unfold FastSpec
  dsimp only
  rw [hnlv, hnllv, abs_neg]
  refine ⟨hnlf, hnllf, hcf, le_trans (by norm_num) hc1, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 ≤ 2 ^ 1000)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 50)]
  · linarith [(by norm_num : (746 : ℝ) ≤ 2 ^ 1020)]
  · have h4 : (|b| + value (Float.ofBits 0x3B66AAD80C11872C).toBits) / 2 ^ 52 ≤
        (1 / 2 ^ 21 + 1 / 2 ^ 72) / 2 ^ 52 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h5 : (50 : ℝ) / 2 ^ 54 ≤ |L| / 2 ^ 54 := div_le_div_of_nonneg_right hL1 (by positivity)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 73 + (1 / 2 ^ 69 + 745 / 2 ^ 78) + 2 * (1 / 2 ^ 72) +
      (1 / 2 ^ 21 + 1 / 2 ^ 72) / 2 ^ 52 ≤ 50 / 2 ^ 54)]

#print axioms tiny_spec

end Verified.Examples.LgammaFastTiny
