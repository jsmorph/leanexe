import Verified.Examples.TgammaTop
import Verified.Examples.TgammaSpecial
import Verified.Examples.TgammaRecip
import Verified.Examples.TgammaWords
import LeanExe.ProofKit.F64RelativeStep
import LeanExe.ProofKit.GammaBasic

/-!
**The path of `tgammaWith` below `2 ^ -112`** within one step of `Γ`.  `GammaBasic.gamma_sub_inv_bounds`
puts `Γ x` within `8/5` of `1/x`, which is at least `2 ^ 112` in magnitude.  For `|x| > 2 ^ -1024`
the quotient `1/x` lies below `2 ^ 1024 - 2 ^ 971`, so `TgammaTop.div_top` bounds its rounding by
`2 ^ -53` relative, and the result is within `11/8` units of roundoff of `Γ x`
(`F64RelativeStep.within_one_relative`).  When the fused multiply-add finds `r x = 1`, the code
returns `r - 1/2`: then `|r x - 1| ≤ 2 ^ -1075` under `FmaNearest`, so `r` lies within `1/2` of
`1/x`, and the rounded `r - 1/2` is again close enough.  For `|x| ≤ 2 ^ -1024` the quotient is an
infinity (`TgammaTop.div_overflow`), subtracting `1/2` keeps it, and `|Γ x|` is at least the overflow
threshold, whose reference is the same infinity.  At `x = 2 ^ -1024` the code adds two words whose sum
is the threshold itself, which rounds to `+∞` (`add_overflow`).
-/

namespace Verified.Examples.TgammaTiny
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD TgammaTop TgammaRecip TgammaFloor
  TgammaWords

set_option exponentiation.threshold 4096

/-- A sum at or above the overflow threshold rounds to `+∞`. -/
theorem add_overflow (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h : 2 ^ 1024 - 2 ^ 970 ≤ value a + value b) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.infinity false := by
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := ⟨_, rfl⟩
  have hSv : value a + value b = (S : ℝ) / 2 ^ 1074 := by rw [value, value, hS]; push_cast; ring
  have hSlo : (2 : ℝ) ^ 2098 - 2 ^ 2044 ≤ S := by
    rw [hSv, le_div_iff₀ (by positivity)] at h
    linarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2044)]
  have hSpos : 0 < S := by
    have : (0 : ℝ) < S := lt_of_lt_of_le (by norm_num) hSlo
    exact_mod_cast this
  have hb0 : (S == 0) = false := by simpa using hSpos.ne'
  have hadd : Wasm.IEEE64.add a b = Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) S.natAbs := by
    simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false, ← hS, hb0]
  rw [hadd, decide_eq_false (not_lt.mpr hSpos.le)]
  apply F64Saturate.round_overflow
  have h1 : ((S.natAbs : ℕ) : ℝ) = S := by rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hSpos)]
  have h2 : ((2 ^ 2098 - 2 ^ 2044 : ℕ) : ℝ) = 2 ^ 2098 - 2 ^ 2044 := by norm_num
  have : ((2 ^ 2098 - 2 ^ 2044 : ℕ) : ℝ) ≤ ((S.natAbs : ℕ) : ℝ) := by rw [h1, h2]; exact hSlo
  exact_mod_cast this

/-- `+∞` is within one step of every real at or above the overflow threshold. -/
theorem within_pos_inf (y : ℝ) (hy : F64PositiveRounding.overflowThreshold ≤ y) :
    F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.infinity false) := by
  have hy0 : 0 ≤ y := le_trans F64PositiveRounding.threshold_positive.le hy
  unfold F64SignedRounding.WithinSteps F64SignedRounding.roundNearestEven
  rw [ite_eq_left hy0, F64PositiveRounding.reference_overflow y hy,
    show Wasm.IEEE64.infinity false = F64PositiveRounding.positiveInfinity by decide]
  refine ⟨by decide, ?_⟩
  simp

/-- `-∞` is within one step of every real at or below the negated threshold. -/
theorem within_neg_inf (y : ℝ) (hy : y ≤ -F64PositiveRounding.overflowThreshold) :
    F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.infinity true) := by
  have hy0 : ¬ 0 ≤ y := by
    have := F64PositiveRounding.threshold_positive
    intro h
    linarith
  unfold F64SignedRounding.WithinSteps F64SignedRounding.roundNearestEven
  rw [ite_eq_right hy0, F64PositiveRounding.reference_overflow (-y) (by linarith),
    show Wasm.IEEE64.infinity true =
      Wasm.IEEE64.negate F64PositiveRounding.positiveInfinity by decide]
  refine ⟨by decide, ?_⟩
  simp

/-- An infinity minus a finite word is the same infinity. -/
theorem sub_inf (neg : Bool) (b : UInt64) (hb : Finite b) :
    Wasm.IEEE64.sub (Wasm.IEEE64.infinity neg) b = Wasm.IEEE64.infinity neg := by
  obtain ⟨hnf, -⟩ := F64Magnitude.negate_value b hb
  have h1 : Wasm.IEEE64.isNaN (Wasm.IEEE64.infinity neg) = false := by cases neg <;> decide
  have h2 : Wasm.IEEE64.isInfinite (Wasm.IEEE64.infinity neg) = true := by cases neg <;> decide
  simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, h1, h2, not_nan_of_finite hnf,
    not_infinite_of_finite hnf, Bool.or_false, Bool.false_and, Bool.false_eq_true, ite_false,
    ite_true]

theorem half_bits : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl

theorem half_finite : Finite (0.5 : Float).toBits := by
  rw [half_bits]; unfold CodeLib.IEEE64.Finite; decide

theorem half_value : value (0.5 : Float).toBits = 1 / 2 := by
  rw [half_bits, TgammaSpecial.lit_value 0x3FE0000000000000 (1 / 2) (by decide +kernel)]
  norm_num

theorem one_mag : Wasm.IEEE64.scaledMagnitude (1.0 : Float).toBits ≠ 0 := by
  rw [TgammaSpecial.one_bits]; decide

theorem one_sign : Wasm.IEEE64.sign (1.0 : Float).toBits = false := by
  rw [TgammaSpecial.one_bits]; decide

/-- The result of a nearest fused multiply-add that is zero: the exact value is at most half the
least subnormal. -/
theorem fma_zero (hF : FmaSpec.FmaNearest) (a b c : Float) (ha : Finite a.toBits)
    (hb : Finite b.toBits) (hc : Finite c.toBits)
    (hS : |value a.toBits * value b.toBits + value c.toBits| ≤ 2 ^ 1023)
    (h0 : (Fma.fma a b c == 0.0) = true) :
    |value a.toBits * value b.toBits + value c.toBits| ≤ 1 / 2 ^ 1075 := by
  obtain ⟨hf, hn⟩ := hF a b c ha hb hc hS
  have hv0 : value (Fma.fma a b c).toBits = 0 := (TgammaSpecial.zero_test _ hf).mp h0
  set S := value a.toBits * value b.toBits + value c.toBits
  have hp : value (1 : UInt64) = 1 / 2 ^ 1074 := by
    rw [TgammaSpecial.lit_value 1 (1 / 2 ^ 1074) (by decide +kernel)]
    norm_num
  have hm : value (0x8000000000000001 : UInt64) = -(1 / 2 ^ 1074) := by
    rw [TgammaSpecial.lit_value 0x8000000000000001 (-(1 / 2 ^ 1074)) (by decide +kernel)]
    norm_num
  have h1 := hn 1 (by unfold CodeLib.IEEE64.Finite; decide)
  have h2 := hn 0x8000000000000001 (by unfold CodeLib.IEEE64.Finite; decide)
  rw [hv0, zero_sub, abs_neg, hp] at h1
  rw [hv0, zero_sub, abs_neg, hm] at h2
  rcases le_total 0 S with hS0 | hS0
  · rw [abs_of_nonneg hS0] at h1 ⊢
    rcases le_total S (1 / 2 ^ 1074) with h3 | h3
    · rw [abs_of_nonneg (by linarith)] at h1
      linarith
    · rw [abs_of_nonpos (by linarith)] at h1
      linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 1074)]
  · rw [abs_of_nonpos hS0] at h2 ⊢
    rcases le_total (-(1 / 2 ^ 1074)) S with h3 | h3
    · rw [abs_of_nonpos (by linarith)] at h2
      linarith
    · rw [abs_of_nonneg (by linarith)] at h2
      linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 1074)]

/-- **The path below `2 ^ -112`** within one step of `Γ`. -/
theorem tinyPath_within (hF : FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (hx0 : value x.toBits ≠ 0) (hsmall : |value x.toBits| < 1 / 2 ^ 112) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.tinyPath x).toBits := by
  set vx := value x.toBits with hvx
  have hax : 0 < |vx| := abs_pos.mpr hx0
  have hax' : |vx| ≠ 0 := hax.ne'
  obtain ⟨hglo, hghi⟩ := GammaBasic.gamma_sub_inv_bounds hx0
    (by linarith [neg_abs_le vx, (by norm_num : (1 : ℝ) / 2 ^ 112 ≤ 1 / 2)])
    (by linarith [le_abs_self vx, (by norm_num : (1 : ℝ) / 2 ^ 112 ≤ 1)])
  set G := Real.Gamma vx with hG
  have hR : |1 / vx| = 1 / |vx| := by rw [abs_div, abs_one]
  have hR112 : 2 ^ 112 ≤ |1 / vx| := by
    rw [hR, le_div_iff₀ hax]
    nlinarith [(by norm_num : (2 : ℝ) ^ 112 * (1 / 2 ^ 112) = 1)]
  have hGd : |G - 1 / vx| ≤ 8 / 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hthr : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
  unfold TgammaBranches.tinyPath
  by_cases hw : (x.toBits == 0x0004000000000000) = true
  · -- `x = 2 ^ -1024`: the sum of two words rounds to `+∞`
    rw [ite_eq_left hw]
    have hxw : x.toBits = 0x0004000000000000 := by simpa using hw
    have hvxv : vx = 1 / 2 ^ 1024 := by
      rw [hvx, hxw, TgammaSpecial.lit_value 0x0004000000000000 (1 / 2 ^ 1024) (by decide +kernel)]
      norm_num
    have hf1 : Wasm.IEEE64.isFinite 0x7FEFFFFFFFFFFFFF = true := by decide
    have hf2 : Wasm.IEEE64.isFinite 0x7C90000000000000 = true := by decide
    rw [F64Bits.toBits_add, ofBits_bits _ hf1, ofBits_bits _ hf2,
      add_overflow _ _ hf1 hf2 (by
        rw [TgammaSpecial.lit_value 0x7FEFFFFFFFFFFFFF ((2 ^ 53 - 1) * 2 ^ 971) (by decide +kernel),
          TgammaSpecial.lit_value 0x7C90000000000000 (2 ^ 970) (by decide +kernel)]
        norm_num)]
    apply within_pos_inf
    rw [hthr]
    have : 1 / vx = 2 ^ 1024 := by rw [hvxv]; norm_num
    linarith
  rw [ite_eq_right hw]
  dsimp only
  have hz : ¬ ((x == 0.0) = true) := by rw [TgammaSpecial.zero_test x hx]; exact hx0
  rw [ite_eq_right hz]
  obtain ⟨hnf, hnv⟩ := neg_float 1.0 one_finite
  rw [one_value] at hnv
  by_cases hbig : |vx| ≤ 1 / 2 ^ 1024
  · -- the quotient overflows
    have hq : 2 ^ 1024 ≤ |value (1.0 : Float).toBits / vx| := by
      rw [one_value, hR, le_div_iff₀ hax]
      nlinarith [(by norm_num : (2 : ℝ) ^ 1024 * (1 / 2 ^ 1024) = 1)]
    have hmx : Wasm.IEEE64.scaledMagnitude x.toBits ≠ 0 := by
      intro h0
      apply hx0
      have := F64RoundNearest.abs_value x.toBits
      rw [h0] at this
      simpa using this
    have hdiv : (1.0 / x).toBits = Wasm.IEEE64.infinity (Wasm.IEEE64.sign x.toBits) := by
      rw [F64Bits.toBits_div, div_overflow _ _ one_finite hx one_mag hmx hq, one_sign]
      simp
    have hres : (if (Fma.fma (1.0 / x) x (-1.0) == 0.0) = true then 1.0 / x - 0.5 else 1.0 / x).toBits =
        Wasm.IEEE64.infinity (Wasm.IEEE64.sign x.toBits) := by
      split_ifs
      · rw [F64Bits.toBits_sub, hdiv, sub_inf _ _ half_finite]
      · exact hdiv
    rw [hres]
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hs : Wasm.IEEE64.sign x.toBits = true := by
        rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x.toBits) with h | h
        · exact h
        · have := F64TwoSum.value_nonneg_of_sign x.toBits h
          linarith
      rw [hs]
      apply within_neg_inf
      rw [hthr]
      have : 1 / vx ≤ -2 ^ 1024 := by
        rw [div_le_iff_of_neg hneg]
        rw [abs_of_neg hneg] at hbig
        nlinarith [(by norm_num : (2 : ℝ) ^ 1024 * (1 / 2 ^ 1024) = 1)]
      linarith
    · have hs : Wasm.IEEE64.sign x.toBits = false := by
        rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x.toBits) with h | h
        · have := F64TwoSum.value_nonpos_of_sign x.toBits h
          linarith
        · exact h
      rw [hs]
      apply within_pos_inf
      rw [hthr]
      have : 2 ^ 1024 ≤ 1 / vx := by
        rw [le_div_iff₀ hpos]
        rw [abs_of_pos hpos] at hbig
        nlinarith [(by norm_num : (2 : ℝ) ^ 1024 * (1 / 2 ^ 1024) = 1)]
      linarith
  -- the quotient is finite
  push Not at hbig
  have hmx : Wasm.IEEE64.scaledMagnitude x.toBits ≠ 0 := by
    intro h0
    apply hx0
    have := F64RoundNearest.abs_value x.toBits
    rw [h0] at this
    simpa using this
  have hgrid : 1 / 2 ^ 1024 + 1 / 2 ^ 1074 ≤ |vx| := by
    have h := F64RoundNearest.abs_value x.toBits
    rw [← hvx] at h
    rw [h] at hbig ⊢
    have h1 : (2 : ℝ) ^ 50 < Wasm.IEEE64.scaledMagnitude x.toBits := by
      rw [lt_div_iff₀ (by positivity)] at hbig
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1024 * 2 ^ 1074 = 2 ^ 50)]
    have h2 : 2 ^ 50 < Wasm.IEEE64.scaledMagnitude x.toBits := by exact_mod_cast h1
    have h3 : ((2 ^ 50 + 1 : ℕ) : ℝ) ≤ Wasm.IEEE64.scaledMagnitude x.toBits := by
      exact_mod_cast h2
    push_cast at h3
    rw [le_div_iff₀ (by positivity)]
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 1024 + 1 / 2 ^ 1074) * 2 ^ 1074 = 2 ^ 50 + 1)]
  have hqhi : |value (1.0 : Float).toBits / vx| < 2 ^ 1024 - 2 ^ 971 := by
    rw [one_value, hR, div_lt_iff₀ hax]
    nlinarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 971) * (1 / 2 ^ 1024 + 1 / 2 ^ 1074) > 1)]
  have hqlo : 1 ≤ |value (1.0 : Float).toBits / vx| := by
    rw [one_value]; linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 112)]
  obtain ⟨hrf, hre⟩ := fdiv_top 1.0 x one_finite hx one_mag hmx hqlo hqhi
  rw [one_value] at hre
  set r := 1.0 / x with hrdef
  set vr := value r.toBits with hvr
  have hG112 : 2 ^ 112 - 2 ≤ |G| := by
    have := abs_sub_abs_le_abs_sub (1 / vx) G
    rw [abs_sub_comm] at this
    linarith
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  by_cases hfz : (Fma.fma r x (-1.0) == 0.0) = true
  · -- `r x = 1` to within half the least subnormal: the code returns `r - 1/2`
    rw [ite_eq_left hfz]
    have hrb : |vr| ≤ 2 * |1 / vx| := by
      have := abs_sub_abs_le_abs_sub vr (1 / vx)
      have : |1 / vx| / 2 ^ 53 ≤ |1 / vx| := div_le_self (abs_nonneg _) (by norm_num)
      linarith
    have hfS : |vr * vx + -1| ≤ 2 ^ 1023 := by
      have h1 : |vr * vx| ≤ 2 := by
        rw [abs_mul]
        calc |vr| * |vx| ≤ 2 * |1 / vx| * |vx| := mul_le_mul_of_nonneg_right hrb (abs_nonneg _)
          _ = 2 := by rw [hR]; field_simp
      have := abs_add_le (vr * vx) (-1)
      rw [abs_neg, abs_one] at this
      linarith [(by norm_num : (3 : ℝ) ≤ 2 ^ 1023)]
    have hz0 := fma_zero hF r x (-1.0) hrf hx hnf (by rw [hnv]; exact hfS) hfz
    rw [hnv] at hz0
    -- `|r - 1/x| ≤ 1/2`
    have hrx : |vr - 1 / vx| ≤ 1 / 2 := by
      have hid : vr - 1 / vx = (vr * vx + -1) / vx := by field_simp; ring
      rw [hid, abs_div, div_le_iff₀ hax]
      have h4 : (1 : ℝ) / 2 ^ 1074 ≤ |vx| := by linarith [hgrid, (by positivity : (0 : ℝ) < 1 / 2 ^ 1024)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 = 1 / 2 * (1 / 2 ^ 1074))]
    have hS : |vr - 1 / 2| ≤ |G| + 13 / 5 := by
      have := abs_sub_abs_le_abs_sub (vr - 1 / 2) G
      have h5 : |vr - 1 / 2 - G| ≤ 13 / 5 := by
        have := abs_add_le (vr - 1 / vx) (1 / vx - G)
        rw [show vr - 1 / vx + (1 / vx - G) = vr - G by ring, abs_sub_comm (1 / vx)] at this
        have := abs_sub (vr - G) (1 / 2)
        rw [show vr - G - 1 / 2 = vr - 1 / 2 - G by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          at this
        linarith
      linarith
    have hS0 : vr - 1 / 2 ≠ 0 := by
      intro h0
      have h6 : |vr - 1 / 2 - G| ≤ 13 / 5 := by
        have := abs_add_le (vr - 1 / vx) (1 / vx - G)
        rw [show vr - 1 / vx + (1 / vx - G) = vr - G by ring, abs_sub_comm (1 / vx)] at this
        have := abs_sub (vr - G) (1 / 2)
        rw [show vr - G - 1 / 2 = vr - 1 / 2 - G by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          at this
        linarith
      rw [h0, zero_sub, abs_neg] at h6
      linarith [(by norm_num : (13 : ℝ) / 5 < 2 ^ 112 - 2)]
    have hSmax : |vr - 1 / 2| < 2 ^ 1024 - 2 ^ 971 := by
      have := abs_sub (vr) (1 / 2)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      have h7 : |vr| ≤ |1 / vx| * (1 + 1 / 2 ^ 53) := by
        have := abs_sub_abs_le_abs_sub vr (1 / vx)
        linarith
      have h8 : |1 / vx| ≤ 2 ^ 1024 - 2 ^ 972 := by
        rw [one_value] at hqhi
        rw [hR, div_le_iff₀ hax]
        nlinarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 972) * (1 / 2 ^ 1024 + 1 / 2 ^ 1074) ≥ 1)]
      nlinarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 972) * (1 + 1 / 2 ^ 53) + 1 / 2 <
        2 ^ 1024 - 2 ^ 971)]
    obtain ⟨hcf, hce⟩ := fsub_top r 0.5 hrf half_finite (by rw [half_value]; exact hS0)
      (by rw [half_value]; exact hSmax)
    rw [half_value] at hce
    apply F64RelativeStep.within_one_relative G _ hcf
      (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 2 ^ 112 - 2)])
    rw [hu]
    have h9 : |value (r - 0.5).toBits - G| ≤ (|G| + 13 / 5) / 2 ^ 53 + 13 / 5 := by
      have h10 : |vr - 1 / 2 - G| ≤ 13 / 5 := by
        have := abs_add_le (vr - 1 / vx) (1 / vx - G)
        rw [show vr - 1 / vx + (1 / vx - G) = vr - G by ring, abs_sub_comm (1 / vx)] at this
        have := abs_sub (vr - G) (1 / 2)
        rw [show vr - G - 1 / 2 = vr - 1 / 2 - G by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          at this
        linarith
      have := abs_add_le (value (r - 0.5).toBits - (vr - 1 / 2)) (vr - 1 / 2 - G)
      rw [show value (r - 0.5).toBits - (vr - 1 / 2) + (vr - 1 / 2 - G) =
        value (r - 0.5).toBits - G by ring] at this
      have : |vr - 1 / 2| / 2 ^ 53 ≤ (|G| + 13 / 5) / 2 ^ 53 :=
        div_le_div_of_nonneg_right hS (by norm_num)
      linarith
    nlinarith [(by norm_num : (13 : ℝ) / 5 / 2 ^ 53 + 13 / 5 ≤ 3 / 8 / 2 ^ 53 * (2 ^ 112 - 2))]
  · -- the code returns `r`
    rw [ite_eq_right hfz]
    apply F64RelativeStep.within_one_relative G _ hrf
      (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 2 ^ 112 - 2)])
    rw [hu]
    have h1 : |1 / vx| ≤ |G| + 8 / 5 := by
      have := abs_sub_abs_le_abs_sub (1 / vx) G
      rw [abs_sub_comm (1 / vx)] at this
      linarith
    have := abs_add_le (vr - 1 / vx) (1 / vx - G)
    rw [show vr - 1 / vx + (1 / vx - G) = vr - G by ring, abs_sub_comm (1 / vx)] at this
    have : |1 / vx| / 2 ^ 53 ≤ (|G| + 8 / 5) / 2 ^ 53 := div_le_div_of_nonneg_right h1 (by norm_num)
    nlinarith [(by norm_num : (8 : ℝ) / 5 / 2 ^ 53 + 8 / 5 ≤ 3 / 8 / 2 ^ 53 * (2 ^ 112 - 2))]

#print axioms add_overflow
#print axioms fma_zero
#print axioms tinyPath_within

end Verified.Examples.TgammaTiny
