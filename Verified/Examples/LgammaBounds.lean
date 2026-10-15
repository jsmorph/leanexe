import Verified.Examples.LgammaAccGrowth
import Verified.Examples.LgammaApprox
import Verified.Examples.LgammaReflMid
import Verified.Examples.LgammaEndCell

/-!
Bounds on `ln |Γ x|` at the doubles where `Lgamma.accurate` runs: `|ln |Γ x||` lies from `2^-1000`
to `2^1020` at every finite `x` with `|x| ≤ 2^800` other than 0, 1, 2, and the negative integers
(`lgamma_bounds`), the hypotheses `hL1` and `hL2` of `LgammaAccPath.accurate_within`.  Below
`-21/2` the lower bound comes from `LgammaApprox.CancelFact` and `LgammaAccGrowth.growth_large`.
From `-21/2` to `-2` the 17 intervals of `LgammaApprox.rootRanges` cover every double other than
the integers, the half-integers from `-19/2` to `-7/2`, and `sxBound`, so `RootMinFact`,
`LgammaAccLower.lower_half`, and `LgammaAccLower.lower_sxb` give `2^-60` (`neg_root`).  Near 1
and 2 the convexity of `ln Γ` and the chords of `LgammaAccLower.gamma_upper` and `gamma_upper2`
give `|ln Γ x| ≥ 0.2274 |x - c|`, and a double other than `c` lies at least `2^-53` from it
(`near_one`, `near_two`).  `LgammaAccLower` bounds the other ranges from below by `1/20`.  The
upper bound comes from `LgammaAccGrowth.lgamma_upper` above 2, the recurrence below 2, and the
reflection with `sin (π φ)/π ≥ min (φ, 1 - φ)/2` below 0, where the fractional part `φ` of a
double is a multiple of `2^-1074`.
-/

namespace Verified.Examples.LgammaBounds
open CodeLib.IEEE64 LeanExe.ProofKit GammaBasic Real

set_option exponentiation.threshold 4096

/-! ### Words next to 1 and 2 -/

theorem pos_word (w : UInt64) (h : 0 < value w) : w.toNat < 2 ^ 63 := by
  have hs := F64Exact.sign_of_pos w h
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
  exact hs

theorem above_word (w c : UInt64) (hw : w.toNat < 2 ^ 63) (hc : c.toNat + 1 < 2 ^ 63)
    (h : value c < value w) : value (UInt64.ofNat (c.toNat + 1)) ≤ value w := by
  have hc1 : (UInt64.ofNat (c.toNat + 1)).toNat = c.toNat + 1 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hlt : c.toNat < w.toNat := by
    by_contra hn
    push Not at hn
    have := LgammaEndCell.value_mono (by omega : c.toNat < 2 ^ 63) hn
    linarith
  exact LgammaEndCell.value_mono hw (by rw [hc1]; omega)

theorem below_word (w c : UInt64) (hw : w.toNat < 2 ^ 63) (hc : c.toNat < 2 ^ 63)
    (hc1 : 1 ≤ c.toNat) (h : value w < value c) :
    value w ≤ value (UInt64.ofNat (c.toNat - 1)) := by
  have hcm : (UInt64.ofNat (c.toNat - 1)).toNat = c.toNat - 1 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hlt : w.toNat < c.toNat := by
    by_contra hn
    push Not at hn
    have := LgammaEndCell.value_mono hw hn
    linarith
  exact LgammaEndCell.value_mono (by rw [hcm]; omega) (by rw [hcm]; omega)

theorem word_val (w : UInt64) (q : ℚ) (h : PolyBound.ratOfWord w = q) : value w = (q : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, h]

/-- A positive double other than 1 lies at least `2^-53` from 1. -/
theorem gap_one (w : UInt64) (h0 : 0 < value w) (hne : value w ≠ 1) :
    1 / 2 ^ 53 ≤ |value w - 1| := by
  have hw := pos_word w h0
  have h1 : value (0x3FF0000000000000 : UInt64) = 1 := by
    rw [word_val _ 1 (by decide +kernel)]; norm_num
  rcases lt_or_gt_of_ne hne with h | h
  · have hb := below_word w 0x3FF0000000000000 hw (by decide) (by decide) (by rw [h1]; exact h)
    have e : value (UInt64.ofNat ((0x3FF0000000000000 : UInt64).toNat - 1)) =
        ((1 - 1 / 2 ^ 53 : ℚ) : ℝ) := word_val _ _ (by decide +kernel)
    rw [e] at hb
    push_cast at hb
    rw [abs_of_neg (by linarith)]
    linarith
  · have ha := above_word w 0x3FF0000000000000 hw (by decide) (by rw [h1]; exact h)
    have e : value (UInt64.ofNat ((0x3FF0000000000000 : UInt64).toNat + 1)) =
        ((1 + 1 / 2 ^ 52 : ℚ) : ℝ) := word_val _ _ (by decide +kernel)
    rw [e] at ha
    push_cast at ha
    rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 52)]

/-- A positive double other than 2 lies at least `2^-52` from 2. -/
theorem gap_two (w : UInt64) (h0 : 0 < value w) (hne : value w ≠ 2) :
    1 / 2 ^ 52 ≤ |value w - 2| := by
  have hw := pos_word w h0
  have h2 : value (0x4000000000000000 : UInt64) = 2 := by
    rw [word_val _ 2 (by decide +kernel)]; norm_num
  rcases lt_or_gt_of_ne hne with h | h
  · have hb := below_word w 0x4000000000000000 hw (by decide) (by decide) (by rw [h2]; exact h)
    have e : value (UInt64.ofNat ((0x4000000000000000 : UInt64).toNat - 1)) =
        ((2 - 1 / 2 ^ 52 : ℚ) : ℝ) := word_val _ _ (by decide +kernel)
    rw [e] at hb
    push_cast at hb
    rw [abs_of_neg (by linarith)]
    linarith
  · have ha := above_word w 0x4000000000000000 hw (by decide) (by rw [h2]; exact h)
    have e : value (UInt64.ofNat ((0x4000000000000000 : UInt64).toNat + 1)) =
        ((2 + 1 / 2 ^ 51 : ℚ) : ℝ) := word_val _ _ (by decide +kernel)
    rw [e] at ha
    push_cast at ha
    rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1 / 2 ^ 51)]

/-! ### Near 1 and 2 -/

theorem lgamma_le_chord (u c : ℝ) (hu : 0 < u) (hG : Gamma u ≤ 1 - c) (hc : c < 1) :
    lgamma u ≤ -c := by
  have hg := Real.Gamma_pos_of_pos hu
  have h1 := Real.log_le_log hg hG
  have h2 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - c)
  unfold lgamma
  linarith

theorem slope (x y z : ℝ) (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    (lgamma y - lgamma x) / (y - x) ≤ (lgamma z - lgamma y) / (z - y) :=
  Real.convexOn_log_Gamma.slope_mono_adjacent (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith)) hxy hyz

theorem lg54 : lgamma (5 / 4) ≤ -(2274 / 10000 / 4) :=
  lgamma_le_chord (5 / 4) (2274 / 10000 / 4) (by norm_num)
    (by have := LgammaAccLower.gamma_upper (5 / 4) (by norm_num) (by norm_num); linarith)
    (by norm_num)

theorem lg74 : lgamma (7 / 4) ≤ -(2274 / 10000 / 4) :=
  lgamma_le_chord (7 / 4) (2274 / 10000 / 4) (by norm_num)
    (by have := LgammaAccLower.gamma_upper2 (7 / 4) (by norm_num) (by norm_num); linarith)
    (by norm_num)

/-- `|ln Γ x| ≥ 0.2274 |x - 1|` from 3/4 to 5/4. -/
theorem near_one (x : ℝ) (h1 : 3 / 4 ≤ x) (h2 : x ≤ 5 / 4) :
    2274 / 10000 * |x - 1| ≤ |lgamma x| := by
  rcases lt_trichotomy x 1 with h | h | h
  · have hs := slope x 1 (5 / 4) (by linarith) h (by norm_num)
    rw [lgamma_one] at hs
    have hd : 0 < 1 - x := by linarith
    rw [div_le_div_iff₀ hd (by norm_num)] at hs
    have := lg54
    rw [abs_of_neg (by linarith : x - 1 < 0)]
    have hpos : 0 ≤ lgamma x := by nlinarith
    rw [abs_of_nonneg hpos]
    nlinarith
  · rw [h, sub_self, abs_zero, mul_zero]
    exact abs_nonneg _
  · have hc := lgamma_le_chord x (2274 / 10000 * (x - 1)) (by linarith)
      (LgammaAccLower.gamma_upper x h (by linarith)) (by nlinarith)
    rw [abs_of_pos (by linarith : 0 < x - 1)]
    have : 0 ≤ 2274 / 10000 * (x - 1) := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- `|ln Γ x| ≥ 0.2274 |x - 2|` from 7/4 to 9/4. -/
theorem near_two (x : ℝ) (h1 : 7 / 4 ≤ x) (h2 : x ≤ 9 / 4) :
    2274 / 10000 * |x - 2| ≤ |lgamma x| := by
  rcases lt_trichotomy x 2 with h | h | h
  · have hc := lgamma_le_chord x (2274 / 10000 * (2 - x)) (by linarith)
      (LgammaAccLower.gamma_upper2 x (by linarith) h) (by nlinarith)
    rw [abs_of_neg (by linarith : x - 2 < 0)]
    have : 0 ≤ 2274 / 10000 * (2 - x) := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [h, sub_self, abs_zero, mul_zero]
    exact abs_nonneg _
  · have hs := slope (7 / 4) 2 x (by norm_num) (by norm_num) h
    rw [lgamma_two] at hs
    have hd : 0 < x - 2 := by linarith
    rw [div_le_div_iff₀ (by norm_num) hd] at hs
    have := lg74
    rw [abs_of_pos hd]
    have hpos : 0 ≤ lgamma x := by nlinarith
    rw [abs_of_nonneg hpos]
    nlinarith

/-! ### From `-21/2` to `-2` -/

/-- **The ranges of the polynomials about the negative zeros** cover `(-21/2, -2)` up to their
ends, which are integers, half-integers, and `sxBound`: `|ln |Γ x|| ≥ 2^-60` at every
non-integer double there. -/
theorem neg_root (hRM : LgammaApprox.RootMinFact) (w : UInt64) (hw : Finite w)
    (hint : ∀ n : ℤ, value w ≠ n) (h1 : -(21 / 2) < value w) (h2 : value w < -2) :
    1 / 2 ^ 60 ≤ |lgamma (value w)| := by
  set v := value w with hv
  by_cases hI0 : ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) < v
  · exact hRM 0x3FB7400000000000 (PolyBound.ratOfWord 0xC004E147AE147AE1) (-2) 128 26 6 3
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI0
  rcases hI0.lt_or_eq with hI0 | hE0
  swap
  · rw [hE0]
    exact le_trans (by norm_num) LgammaAccLower.lower_sxb
  by_cases hI1 : (-3 : ℝ) < v
  · exact hRM 0x3FB1680000000000 (-3) (PolyBound.ratOfWord 0xC004E147AE147AE1) 183 27 6 4
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI1
  have hI1' : v < (-3 : ℝ) :=
    lt_of_le_of_ne hI1 (fun h => hint (-3) (by rw [h]; norm_num))
  replace hI1 := hI1'
  by_cases hI2 : (-7 / 2 : ℝ) < v
  · exact hRM 0x3FB2D40000000000 (-7 / 2) (-3) 240 20 7 6
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI2
  rcases hI2.lt_or_eq with hI2 | hE2
  swap
  · rw [hE2, show (-7 / 2 : ℝ) = -((3 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 3 (by norm_num) (by norm_num))
  by_cases hI3 : (-4 : ℝ) < v
  · exact hRM 0x3FAEF00000000000 (-4) (-7 / 2) 283 20 7 8
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI3
  have hI3' : v < (-4 : ℝ) :=
    lt_of_le_of_ne hI3 (fun h => hint (-4) (by rw [h]; norm_num))
  replace hI3 := hI3'
  by_cases hI4 : (-9 / 2 : ℝ) < v
  · exact hRM 0x3FC0000000000000 (-9 / 2) (-4) 326 24 7 7
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI4
  rcases hI4.lt_or_eq with hI4 | hE4
  swap
  · rw [hE4, show (-9 / 2 : ℝ) = -((4 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 4 (by norm_num) (by norm_num))
  by_cases hI5 : (-5 : ℝ) < v
  · exact hRM 0x3FB0800000000000 (-5) (-9 / 2) 377 19 7 10
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI5
  have hI5' : v < (-5 : ℝ) :=
    lt_of_le_of_ne hI5 (fun h => hint (-5) (by rw [h]; norm_num))
  replace hI5 := hI5'
  by_cases hI6 : (-11 / 2 : ℝ) < v
  · exact hRM 0x3FB1000000000000 (-11 / 2) (-5) 418 19 6 10
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI6
  rcases hI6.lt_or_eq with hI6 | hE6
  swap
  · rw [hE6, show (-11 / 2 : ℝ) = -((5 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 5 (by norm_num) (by norm_num))
  by_cases hI7 : (-6 : ℝ) < v
  · exact hRM 0x3FC1300000000000 (-6) (-11 / 2) 459 24 6 12
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI7
  have hI7' : v < (-6 : ℝ) :=
    lt_of_le_of_ne hI7 (fun h => hint (-6) (by rw [h]; norm_num))
  replace hI7 := hI7'
  by_cases hI8 : (-13 / 2 : ℝ) < v
  · exact hRM 0x3FC1500000000000 (-13 / 2) (-6) 510 24 6 12
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI8
  rcases hI8.lt_or_eq with hI8 | hE8
  swap
  · rw [hE8, show (-13 / 2 : ℝ) = -((6 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 6 (by norm_num) (by norm_num))
  by_cases hI9 : (-7 : ℝ) < v
  · exact hRM 0x3FC3400000000000 (-7) (-13 / 2) 561 25 6 14
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI9
  have hI9' : v < (-7 : ℝ) :=
    lt_of_le_of_ne hI9 (fun h => hint (-7) (by rw [h]; norm_num))
  replace hI9 := hI9'
  by_cases hI10 : (-15 / 2 : ℝ) < v
  · exact hRM 0x3FC1450000000000 (-15 / 2) (-7) 614 24 6 15
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI10
  rcases hI10.lt_or_eq with hI10 | hE10
  swap
  · rw [hE10, show (-15 / 2 : ℝ) = -((7 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 7 (by norm_num) (by norm_num))
  by_cases hI11 : (-8 : ℝ) < v
  · exact hRM 0x3FC76B0000000000 (-8) (-15 / 2) 665 27 6 17
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI11
  have hI11' : v < (-8 : ℝ) :=
    lt_of_le_of_ne hI11 (fun h => hint (-8) (by rw [h]; norm_num))
  replace hI11 := hI11'
  by_cases hI12 : (-17 / 2 : ℝ) < v
  · exact hRM 0x3FC76C0000000000 (-17 / 2) (-8) 722 27 6 17
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI12
  rcases hI12.lt_or_eq with hI12 | hE12
  swap
  · rw [hE12, show (-17 / 2 : ℝ) = -((8 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 8 (by norm_num) (by norm_num))
  by_cases hI13 : (-9 : ℝ) < v
  · exact hRM 0x3FC9900000000000 (-9) (-17 / 2) 779 28 6 20
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI13
  have hI13' : v < (-9 : ℝ) :=
    lt_of_le_of_ne hI13 (fun h => hint (-9) (by rw [h]; norm_num))
  replace hI13 := hI13'
  by_cases hI14 : (-19 / 2 : ℝ) < v
  · exact hRM 0x3FC9900000000000 (-19 / 2) (-9) 838 28 6 20
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI14
  rcases hI14.lt_or_eq with hI14 | hE14
  swap
  · rw [hE14, show (-19 / 2 : ℝ) = -((9 : ℕ) : ℝ) - 1 / 2 by norm_num]
    exact le_trans (by norm_num)
      (LgammaAccLower.lower_half 9 (by norm_num) (by norm_num))
  by_cases hI15 : (-10 : ℝ) < v
  · exact hRM 0x3FC76B0000000000 (-10) (-19 / 2) 897 27 6 24
      (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)
  push Not at hI15
  have hI15' : v < (-10 : ℝ) :=
    lt_of_le_of_ne hI15 (fun h => hint (-10) (by rw [h]; norm_num))
  replace hI15 := hI15'
  exact hRM 0x3FC76B0000000000 (-21 / 2) (-10) 954 27 6 24
    (by decide +kernel) w hw (by push_cast; linarith) (by push_cast; linarith)

/-! ### The grid of doubles -/

theorem value_eq (w : UInt64) : value w = (Wasm.IEEE64.scaledValue w : ℝ) / 2 ^ 1074 := by
  rw [← PolyBound.ratOfWord_cast]
  simp [PolyBound.ratOfWord]

/-- A nonzero double is at least `2^-1074` in magnitude. -/
theorem abs_min (w : UInt64) (h : value w ≠ 0) : 1 / 2 ^ 1074 ≤ |value w| := by
  rw [value_eq] at h ⊢
  have hm : (Wasm.IEEE64.scaledValue w : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h
    exact h rfl
  have hm' : Wasm.IEEE64.scaledValue w ≠ 0 := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ |(Wasm.IEEE64.scaledValue w : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm'
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- The fractional part of a non-integer double lies from `2^-1074` to `1 - 2^-1074`. -/
theorem fract_min (w : UInt64) (hint : ∀ n : ℤ, value w ≠ n) :
    1 / 2 ^ 1074 ≤ Int.fract (value w) ∧ 1 / 2 ^ 1074 ≤ 1 - Int.fract (value w) := by
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  set n := ⌊value w⌋ with hn
  set k : ℤ := Wasm.IEEE64.scaledValue w - n * 2 ^ 1074 with hk
  have hfk : Int.fract (value w) = (k : ℝ) / 2 ^ 1074 := by
    rw [Int.fract, ← hn, hk, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, sub_div,
      mul_div_cancel_right₀ _ hp.ne', ← value_eq]
  have hf0 : 0 < Int.fract (value w) := Int.fract_pos.mpr (fun h => hint n h)
  have hf1 := Int.fract_lt_one (value w)
  rw [hfk] at hf0 hf1 ⊢
  have hk0 : (0 : ℝ) < k := by
    by_contra hc
    push Not at hc
    have : (k : ℝ) / 2 ^ 1074 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hp.le
    linarith
  have hk1 : (k : ℝ) < 2 ^ 1074 := by
    rw [div_lt_one hp] at hf1
    exact hf1
  have hk0' : 0 < k := by exact_mod_cast hk0
  have hk1' : k < 2 ^ 1074 := by exact_mod_cast hk1
  have ha : (1 : ℝ) ≤ k := by exact_mod_cast hk0'
  have hb : (k : ℝ) ≤ 2 ^ 1074 - 1 := by
    have : k ≤ 2 ^ 1074 - 1 := by omega
    exact_mod_cast this
  constructor
  · exact div_le_div_of_nonneg_right ha hp.le
  · rw [one_sub_div hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) hp.le

theorem log_two_lo : (6931 / 10000 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

theorem log_two_hi : Real.log 2 < 6932 / 10000 := by
  have := Real.log_two_lt_d9
  linarith

/-- `|log y| ≤ 745` from `2^-1074` to `2^52`. -/
theorem abs_log_le (y : ℝ) (h1 : 1 / 2 ^ 1074 ≤ y) (h2 : y ≤ 2 ^ 52) :
    |Real.log y| ≤ 745 := by
  have hy : 0 < y := lt_of_lt_of_le (by positivity) h1
  have a := Real.log_le_log (by positivity) h1
  have b := Real.log_le_log hy h2
  rw [one_div, Real.log_inv, Real.log_pow] at a
  rw [Real.log_pow] at b
  push_cast at a b
  have := log_two_hi
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The bounds -/

/-- Within `1/4` of 0, `ln |Γ x|` is `-ln |x|` within `4 |x|`. -/
theorem small (x : ℝ) (h0 : x ≠ 0) (hx : |x| ≤ 1 / 4) (hmin : 1 / 2 ^ 1074 ≤ |x|) :
    1 / 4 ≤ |lgamma x| ∧ |lgamma x| ≤ 746 := by
  have h := abs_le.mp (abs_lgamma_add_log_le h0 hx)
  have hl : Real.log x = Real.log |x| := (Real.log_abs x).symm
  have hlog := Real.log_le_log (abs_pos.mpr h0) hx
  rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
  push_cast at hlog
  have h2 := log_two_lo
  have hb := abs_log_le |x| hmin (by linarith [(by norm_num : (1 : ℝ) / 4 ≤ 2 ^ 52)])
  have hb' := abs_le.mp hb
  rw [hl] at h
  have hpos : 0 ≤ lgamma x := by linarith
  rw [abs_of_nonneg hpos]
  constructor <;> linarith

/-- **The lower bound** at a double other than 0, 1, 2, and the negative integers. -/
theorem lower_bound (hRM : LgammaApprox.RootMinFact) (hCF : LgammaApprox.CancelFact)
    (w : UInt64) (hw : Finite w) (hint : value w < 0 → ∀ n : ℤ, value w ≠ n)
    (h0 : value w ≠ 0) (h1 : value w ≠ 1) (h2 : value w ≠ 2) :
    1 / 2 ^ 1000 ≤ |lgamma (value w)| := by
  have hmin := abs_min w h0
  set v := value w with hv
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hint' := hint hneg
    by_cases hA : -(1 / 4) ≤ v
    · have := (small v h0 (by rw [abs_of_neg hneg]; linarith) hmin).1
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 4)]
    push Not at hA
    by_cases hB : -2 < v
    · have := LgammaAccLower.lower_neg v hB (by linarith) hint'
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 4)]
    push Not at hB
    have hB' : v < -2 := lt_of_le_of_ne hB (fun h => hint' (-2) (by rw [h]; norm_num))
    by_cases hC : -(21 / 2) < v
    · have := neg_root hRM w hw hint' hC hB'
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 60)]
    push Not at hC
    have hc := hCF w hw (by linarith) hint'
    have hg := LgammaAccGrowth.growth_large (1 - v) (by linarith)
    have : (14 : ℝ) ≤ |lgamma (1 - v)| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h32 : (14 : ℝ) / 2 ^ 32 ≤ |lgamma v| := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 14 / 2 ^ 32)]
  · by_cases hA : v ≤ 1 / 4
    · have := (small v h0 (by rw [abs_of_pos hpos]; exact hA) hmin).1
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 4)]
    push Not at hA
    by_cases hB : v < 3 / 4
    · have := LgammaAccLower.pos_quarter v hA hB
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 20)]
    push Not at hB
    by_cases hC : v ≤ 5 / 4
    · have a := near_one v hB hC
      have b := gap_one w hpos h1
      have : 2274 / 10000 * (1 / 2 ^ 53) ≤ 2274 / 10000 * |v - 1| :=
        mul_le_mul_of_nonneg_left b (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 2274 / 10000 * (1 / 2 ^ 53))]
    push Not at hC
    by_cases hD : v < 7 / 4
    · have := LgammaAccLower.pos_mid v hC hD
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 20)]
    push Not at hD
    by_cases hE : v ≤ 9 / 4
    · have a := near_two v hD hE
      have b := gap_two w hpos h2
      have : 2274 / 10000 * (1 / 2 ^ 52) ≤ 2274 / 10000 * |v - 2| :=
        mul_le_mul_of_nonneg_left b (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 2274 / 10000 * (1 / 2 ^ 52))]
    push Not at hE
    have := LgammaAccLower.pos_large v hE.le
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 20)]

/-- `ln Γ` from `1/4` on, up to `2^802`, lies within `2^812`. -/
theorem pos_upper (y : ℝ) (h1 : 1 / 4 < y) (h2 : y ≤ 2 ^ 802) : |lgamma y| ≤ 2 ^ 812 := by
  by_cases hy : 2 ≤ y
  · have hu := LgammaAccGrowth.lgamma_upper y hy h2
    have hm := Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (le_refl (2 : ℝ)))
      (Set.mem_Ici.mpr hy) hy
    rw [Real.Gamma_two] at hm
    have hl : 0 ≤ lgamma y := Real.log_nonneg hm
    rw [abs_of_nonneg hl]
    exact hu
  push Not at hy
  have hp : 0 < y := by linarith
  have e1 := lgamma_add_one (notPole_of_neg_one_lt (by linarith) hp.ne')
  have e2 := lgamma_add_one (x := y + 1) (notPole_of_neg_one_lt (by linarith) (by linarith))
  have hm1 := Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (le_refl (2 : ℝ)))
    (Set.mem_Ici.mpr (by linarith : (2 : ℝ) ≤ y + 1 + 1)) (by linarith)
  have hm2 := Real.Gamma_strictMonoOn_Ici.monotoneOn
    (Set.mem_Ici.mpr (by linarith : (2 : ℝ) ≤ y + 1 + 1))
    (Set.mem_Ici.mpr (by norm_num : (2 : ℝ) ≤ 4)) (by linarith)
  rw [Real.Gamma_two] at hm1
  have h4 : Real.Gamma 4 = 6 := by
    rw [show (4 : ℝ) = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [h4] at hm2
  have g0 : 0 ≤ lgamma (y + 1 + 1) := Real.log_nonneg hm1
  have g1 : lgamma (y + 1 + 1) ≤ Real.log 6 :=
    Real.log_le_log (Real.Gamma_pos_of_pos (by linarith)) hm2
  have l6 : Real.log 6 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6 / 4)
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow] at this
    push_cast at this
    linarith [log_two_hi]
  have a := abs_le.mp (abs_log_le y (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 4)])
    (by linarith [(by norm_num : (2 : ℝ) ≤ 2 ^ 52)]))
  have b := abs_le.mp (abs_log_le (y + 1) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1)])
    (by linarith [(by norm_num : (3 : ℝ) ≤ 2 ^ 52)]))
  rw [abs_le]
  constructor <;> linarith [(by norm_num : (2 : ℝ) + 745 + 745 ≤ 2 ^ 812)]

/-- **The upper bound** at a nonzero double up to `2^800` in magnitude other than the negative
integers. -/
theorem upper_bound (w : UInt64) (hw : Finite w) (hint : value w < 0 → ∀ n : ℤ, value w ≠ n)
    (h0 : value w ≠ 0) (hbig : |value w| ≤ 2 ^ 800) : |lgamma (value w)| ≤ 2 ^ 1020 := by
  have hmin := abs_min w h0
  set v := value w with hv
  by_cases hs : |v| ≤ 1 / 4
  · have := (small v h0 hs hmin).2
    linarith [(by norm_num : (746 : ℝ) ≤ 2 ^ 1020)]
  push Not at hs
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hint' := hint hneg
    rw [abs_of_neg hneg] at hs hbig
    have h52 : -v < 2 ^ 52 := by
      by_contra hn
      push Not at hn
      obtain ⟨N, hN⟩ :=
        TgammaFloor.int_of_large w hw (by rw [← hv, abs_of_neg hneg]; exact hn)
      exact hint' N hN
    have hr := LgammaReflCore.refl_L v hneg hint'
    have hlg := pos_upper (-v) hs (by linarith [(by norm_num : (2 : ℝ) ^ 52 ≤ 2 ^ 802)])
    obtain ⟨f1, f2⟩ := fract_min w hint'
    set φ := Int.fract v with hφ
    have hJ := LgammaReflMid.s_jordan φ (by linarith) (by linarith)
    have hmn : 1 / 2 ^ 1074 ≤ 1 / 2 - |φ - 1 / 2| := by
      rcases abs_cases (φ - 1 / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
    have hs1 : 1 / 2 ^ 1075 ≤ Real.sin (π * φ) / π := by
      have : (1 / 2 ^ 1074 : ℝ) / 2 ≤ (1 / 2 - |φ - 1 / 2|) / 2 :=
        div_le_div_of_nonneg_right hmn (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 = 1 / 2 ^ 1074 / 2)]
    have hs2 : Real.sin (π * φ) / π ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      linarith [Real.sin_le_one (π * φ), Real.pi_gt_three]
    have hp : 0 < -v * (Real.sin (π * φ) / π) := by
      have : 0 < Real.sin (π * φ) / π := lt_of_lt_of_le (by positivity) hs1
      have : 0 < -v := by linarith
      positivity
    have hlog : |Real.log (-v * (Real.sin (π * φ) / π))| ≤ 2 * 746 := by
      rw [Real.log_mul (by linarith : (0 : ℝ) < -v).ne' (lt_of_lt_of_le (by positivity) hs1).ne']
      have a := abs_le.mp (abs_log_le (-v)
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 4)]) h52.le)
      have b := Real.log_le_log (by positivity) hs1
      have c := Real.log_le_log (lt_of_lt_of_le (by positivity) hs1) hs2
      rw [Real.log_one] at c
      rw [one_div, Real.log_inv, Real.log_pow] at b
      push_cast at b
      have := log_two_hi
      rw [abs_le]
      constructor <;> nlinarith
    show |Real.log (Real.Gamma v)| ≤ 2 ^ 1020
    rw [hr, abs_neg]
    have := abs_add_le (lgamma (-v)) (Real.log (-v * (Real.sin (π * φ) / π)))
    linarith [(by norm_num : (2 : ℝ) ^ 812 + 2 * 746 ≤ 2 ^ 1020)]
  · rw [abs_of_pos hpos] at hs hbig
    have := pos_upper v hs (by linarith [(by norm_num : (2 : ℝ) ^ 800 ≤ 2 ^ 802)])
    linarith [(by norm_num : (2 : ℝ) ^ 812 ≤ 2 ^ 1020)]

/-- **`|ln |Γ x||` from `2^-1000` to `2^1020`** at every finite double up to `2^800` in magnitude
other than 0, 1, 2, and the negative integers. -/
theorem lgamma_bounds (hRM : LgammaApprox.RootMinFact) (hCF : LgammaApprox.CancelFact)
    (w : UInt64) (hw : Finite w) (hint : value w < 0 → ∀ n : ℤ, value w ≠ n)
    (h0 : value w ≠ 0) (h1 : value w ≠ 1) (h2 : value w ≠ 2) (hbig : |value w| ≤ 2 ^ 800) :
    1 / 2 ^ 1000 ≤ |lgamma (value w)| ∧ |lgamma (value w)| ≤ 2 ^ 1020 :=
  ⟨lower_bound hRM hCF w hw hint h0 h1 h2, upper_bound w hw hint h0 hbig⟩

#print axioms gap_one
#print axioms gap_two
#print axioms near_one
#print axioms near_two
#print axioms neg_root
#print axioms fract_min
#print axioms lgamma_bounds

end Verified.Examples.LgammaBounds
