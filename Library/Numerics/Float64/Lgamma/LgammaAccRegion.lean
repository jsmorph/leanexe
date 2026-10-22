import Library.Numerics.Float64.Lgamma.LgammaAccTail
import Library.Numerics.Float64.Lgamma.LgammaAccLower

/-!
**`|log |Γ x|| ≥ 1/20` at the negative arguments from `-21/2` to `-1/4` where `Lgamma.accurate`
selects no polynomial about a zero** (`neg_mid_lower`).  From -2 to -1/4, `LgammaAccLower.lower_neg`
gives `1/4`.  Below -2, a high part `p1` below `3/8` and within `2^-44` of `|log |Γ x||` selects no
range, so either `x` lies in a range's interval with `|p1|` at least the range's bound, which is at
least `3/50`, or `x` is one of the points between the intervals: an integer, which the hypotheses
exclude, a half-integer (`lower_half`), or `sxBound` (`lower_sxb`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccRegion
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

set_option maxHeartbeats 4000000 in
/-- **No polynomial about a zero** from -21/2 to -1/4: `|log |Γ x|| ≥ 1/20`. -/
theorem neg_mid_lower (sx : Float) (hsx : Finite sx.toBits) (hint : ∀ n : ℤ, value sx.toBits ≠ n)
    (h1 : -(21 / 2) < value sx.toBits) (h2 : value sx.toBits ≤ -1 / 4) (p1 : Float)
    (hp1 : Finite p1.toBits)
    (hclose : |value p1.toBits| < 3 / 8 →
      |value p1.toBits| ≤ |GammaBasic.lgamma (value sx.toBits)| * (1 + 1 / 2 ^ 50) + 1 / 2 ^ 44)
    (hfar : 3 / 8 ≤ |value p1.toBits| → 1 / 4 ≤ |GammaBasic.lgamma (value sx.toBits)|)
    (hroot : |value p1.toBits| < 3 / 8 → Lgamma.rootRange p1.abs sx = (0, 0, 0, 0.0)) :
    1 / 20 ≤ |GammaBasic.lgamma (value sx.toBits)| := by
  set v := value sx.toBits with hv
  by_cases hv2 : -2 < v
  · exact le_trans (by norm_num) (LgammaAccLower.lower_neg v hv2 h2 hint)
  by_cases hs : |value p1.toBits| < 3 / 8
  swap
  · exact le_trans (by norm_num) (hfar (not_lt.mp hs))
  have hc := hclose hs
  obtain ⟨haf, hafv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float p1 hp1
  rcases LgammaRootSel.rootRange_spec p1.abs sx haf hsx _ (hroot hs) with
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ |
      ⟨-, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩
  all_goals try exact absurd (congrArg Prod.fst he) (by decide)
  rw [hafv] at n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16
  by_contra hL
  push Not at hL
  have hp : |value p1.toBits| < 3 / 50 := by linarith
  rcases lt_trichotomy v (-(2) : ℝ) with hu0 | he0 | hl0
  rotate_left
  · exact hint (-2) (by rw [he0]; norm_num)
  · exact hv2 hl0
  rcases lt_trichotomy v ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) with hu1 | he1 | hl1
  rotate_left
  · have := LgammaAccLower.lower_sxb
    rw [← he1] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB7400000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FB7400000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n0 ⟨by linarith, hl1, hu0⟩
  rcases lt_trichotomy v (-(3) : ℝ) with hu2 | he2 | hl2
  rotate_left
  · exact hint (-3) (by rw [he2]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB1680000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FB1680000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n1 ⟨by linarith, hl2, hu1⟩
  rcases lt_trichotomy v (-(7 / 2) : ℝ) with hu3 | he3 | hl3
  rotate_left
  · have := LgammaAccLower.lower_half 3 (by norm_num) (by norm_num)
    rw [show -((3 : ℕ) : ℝ) - 1 / 2 = -(7 / 2) by norm_num, ← he3] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FB2D40000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n2 ⟨by linarith, hl3, hu2⟩
  rcases lt_trichotomy v (-(4) : ℝ) with hu4 | he4 | hl4
  rotate_left
  · exact hint (-4) (by rw [he4]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FAEF00000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n3 ⟨by linarith, hl4, hu3⟩
  rcases lt_trichotomy v (-(9 / 2) : ℝ) with hu5 | he5 | hl5
  rotate_left
  · have := LgammaAccLower.lower_half 4 (by norm_num) (by norm_num)
    rw [show -((4 : ℕ) : ℝ) - 1 / 2 = -(9 / 2) by norm_num, ← he5] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC0000000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC0000000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n4 ⟨by linarith, hl5, hu4⟩
  rcases lt_trichotomy v (-(5) : ℝ) with hu6 | he6 | hl6
  rotate_left
  · exact hint (-5) (by rw [he6]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB0800000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FB0800000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n5 ⟨by linarith, hl6, hu5⟩
  rcases lt_trichotomy v (-(11 / 2) : ℝ) with hu7 | he7 | hl7
  rotate_left
  · have := LgammaAccLower.lower_half 5 (by norm_num) (by norm_num)
    rw [show -((5 : ℕ) : ℝ) - 1 / 2 = -(11 / 2) by norm_num, ← he7] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB1000000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FB1000000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n6 ⟨by linarith, hl7, hu6⟩
  rcases lt_trichotomy v (-(6) : ℝ) with hu8 | he8 | hl8
  rotate_left
  · exact hint (-6) (by rw [he8]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC1300000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC1300000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n7 ⟨by linarith, hl8, hu7⟩
  rcases lt_trichotomy v (-(13 / 2) : ℝ) with hu9 | he9 | hl9
  rotate_left
  · have := LgammaAccLower.lower_half 6 (by norm_num) (by norm_num)
    rw [show -((6 : ℕ) : ℝ) - 1 / 2 = -(13 / 2) by norm_num, ← he9] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC1500000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC1500000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n8 ⟨by linarith, hl9, hu8⟩
  rcases lt_trichotomy v (-(7) : ℝ) with hu10 | he10 | hl10
  rotate_left
  · exact hint (-7) (by rw [he10]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC3400000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC3400000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n9 ⟨by linarith, hl10, hu9⟩
  rcases lt_trichotomy v (-(15 / 2) : ℝ) with hu11 | he11 | hl11
  rotate_left
  · have := LgammaAccLower.lower_half 7 (by norm_num) (by norm_num)
    rw [show -((7 : ℕ) : ℝ) - 1 / 2 = -(15 / 2) by norm_num, ← he11] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC1450000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC1450000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n10 ⟨by linarith, hl11, hu10⟩
  rcases lt_trichotomy v (-(8) : ℝ) with hu12 | he12 | hl12
  rotate_left
  · exact hint (-8) (by rw [he12]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76B0000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n11 ⟨by linarith, hl12, hu11⟩
  rcases lt_trichotomy v (-(17 / 2) : ℝ) with hu13 | he13 | hl13
  rotate_left
  · have := LgammaAccLower.lower_half 8 (by norm_num) (by norm_num)
    rw [show -((8 : ℕ) : ℝ) - 1 / 2 = -(17 / 2) by norm_num, ← he13] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76C0000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n12 ⟨by linarith, hl13, hu12⟩
  rcases lt_trichotomy v (-(9) : ℝ) with hu14 | he14 | hl14
  rotate_left
  · exact hint (-9) (by rw [he14]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC9900000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n13 ⟨by linarith, hl14, hu13⟩
  rcases lt_trichotomy v (-(19 / 2) : ℝ) with hu15 | he15 | hl15
  rotate_left
  · have := LgammaAccLower.lower_half 9 (by norm_num) (by norm_num)
    rw [show -((9 : ℕ) : ℝ) - 1 / 2 = -(19 / 2) by norm_num, ← he15] at this
    linarith
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC9900000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n14 ⟨by linarith, hl15, hu14⟩
  rcases lt_trichotomy v (-(10) : ℝ) with hu16 | he16 | hl16
  rotate_left
  · exact hint (-10) (by rw [he16]; norm_num)
  · have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) := by
      have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76B0000000000 := by decide +kernel
      exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
    exact n15 ⟨by linarith, hl16, hu15⟩
  have hl17 : (-(21 / 2) : ℝ) < v := h1
  have hb : (3 / 50 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) := by
    have h : (3 / 50 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76B0000000000 := by decide +kernel
    exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
  exact n16 ⟨by linarith, hl17, hu16⟩

end Library.Numerics.Float64.Lgamma.LgammaAccRegion
