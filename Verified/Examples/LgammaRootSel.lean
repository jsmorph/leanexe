import Verified.Examples.LgammaAccWin

/-!
The selection of `Lgamma.rootRange`, the choice of a polynomial about a negative zero: either the
conditions of the first range in the code's order hold, `|fh|` below the range's bound and `sx`
inside its open interval, and the result is the range's tuple, or no range applies and the result
is `(0, 0, 0, 0.0)`, after which the code keeps its pair (`rootRange_spec`).  The literals of the
interval ends are the negated doubles `2.0` to `10.5` and the double `sxBound` nearest -2.61.
-/

namespace Verified.Examples.LgammaRootSel
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem m2_0 : Finite (-2.0 : Float).toBits ∧ value (-2.0 : Float).toBits = -(2) := by
  have h := LgammaAccWin.lit 2.0 0x4000000000000000 (2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 2.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m3_0 : Finite (-3.0 : Float).toBits ∧ value (-3.0 : Float).toBits = -(3) := by
  have h := LgammaAccWin.lit 3.0 0x4008000000000000 (3) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 3.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m3_5 : Finite (-3.5 : Float).toBits ∧ value (-3.5 : Float).toBits = -(7 / 2) := by
  have h := LgammaAccWin.lit 3.5 0x400C000000000000 (7 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 3.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m4_0 : Finite (-4.0 : Float).toBits ∧ value (-4.0 : Float).toBits = -(4) := by
  have h := LgammaAccWin.lit 4.0 0x4010000000000000 (4) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 4.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m4_5 : Finite (-4.5 : Float).toBits ∧ value (-4.5 : Float).toBits = -(9 / 2) := by
  have h := LgammaAccWin.lit 4.5 0x4012000000000000 (9 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 4.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m5_0 : Finite (-5.0 : Float).toBits ∧ value (-5.0 : Float).toBits = -(5) := by
  have h := LgammaAccWin.lit 5.0 0x4014000000000000 (5) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 5.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m5_5 : Finite (-5.5 : Float).toBits ∧ value (-5.5 : Float).toBits = -(11 / 2) := by
  have h := LgammaAccWin.lit 5.5 0x4016000000000000 (11 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 5.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m6_0 : Finite (-6.0 : Float).toBits ∧ value (-6.0 : Float).toBits = -(6) := by
  have h := LgammaAccWin.lit 6.0 0x4018000000000000 (6) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 6.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m6_5 : Finite (-6.5 : Float).toBits ∧ value (-6.5 : Float).toBits = -(13 / 2) := by
  have h := LgammaAccWin.lit 6.5 0x401A000000000000 (13 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 6.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m7_0 : Finite (-7.0 : Float).toBits ∧ value (-7.0 : Float).toBits = -(7) := by
  have h := LgammaAccWin.lit 7.0 0x401C000000000000 (7) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 7.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m7_5 : Finite (-7.5 : Float).toBits ∧ value (-7.5 : Float).toBits = -(15 / 2) := by
  have h := LgammaAccWin.lit 7.5 0x401E000000000000 (15 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 7.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m8_0 : Finite (-8.0 : Float).toBits ∧ value (-8.0 : Float).toBits = -(8) := by
  have h := LgammaAccWin.lit 8.0 0x4020000000000000 (8) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 8.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m8_5 : Finite (-8.5 : Float).toBits ∧ value (-8.5 : Float).toBits = -(17 / 2) := by
  have h := LgammaAccWin.lit 8.5 0x4021000000000000 (17 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 8.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m9_0 : Finite (-9.0 : Float).toBits ∧ value (-9.0 : Float).toBits = -(9) := by
  have h := LgammaAccWin.lit 9.0 0x4022000000000000 (9) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 9.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m9_5 : Finite (-9.5 : Float).toBits ∧ value (-9.5 : Float).toBits = -(19 / 2) := by
  have h := LgammaAccWin.lit 9.5 0x4023000000000000 (19 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 9.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m10_0 : Finite (-10.0 : Float).toBits ∧ value (-10.0 : Float).toBits = -(10) := by
  have h := LgammaAccWin.lit 10.0 0x4024000000000000 (10) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 10.0 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem m10_5 : Finite (-10.5 : Float).toBits ∧ value (-10.5 : Float).toBits = -(21 / 2) := by
  have h := LgammaAccWin.lit 10.5 0x4025000000000000 (21 / 2) rfl (by decide) (by decide +kernel)
  obtain ⟨f, v⟩ := LgammaAccLow.neg_float 10.5 h.1
  push_cast at h
  exact ⟨f, by rw [v, h.2]⟩

theorem sxb : Finite (Float.ofBits 0xC004E147AE147AE1).toBits ∧
    value (Float.ofBits 0xC004E147AE147AE1).toBits = ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) :=
  ⟨TgammaWords.ofBits_finite _ (by decide), TgammaWords.ofBits_value _ (by decide)⟩

/-- **The selection of `rootRange`**: the first range whose conditions hold, or none. -/
theorem rootRange_spec (afh sx : Float) (haf : Finite afh.toBits) (hsx : Finite sx.toBits)
    (r : UInt64 × UInt64 × UInt64 × Float) (hr : Lgamma.rootRange afh sx = r) :
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FB7400000000000 : ℚ) : ℝ) ∧ ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(2) : ℝ) ∧ r = (128, 26, 6, Float.ofBits 0x4020000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FB1680000000000 : ℚ) : ℝ) ∧ (-(3) : ℝ) < value sx.toBits ∧ value sx.toBits < ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) ∧ r = (183, 27, 6, Float.ofBits 0x4030000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ) ∧ (-(7 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(3) : ℝ) ∧ r = (240, 20, 7, Float.ofBits 0x4050000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ) ∧ (-(4) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(7 / 2) : ℝ) ∧ r = (283, 20, 7, Float.ofBits 0x4070000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC0000000000000 : ℚ) : ℝ) ∧ (-(9 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(4) : ℝ) ∧ r = (326, 24, 7, Float.ofBits 0x4060000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FB0800000000000 : ℚ) : ℝ) ∧ (-(5) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(9 / 2) : ℝ) ∧ r = (377, 19, 7, Float.ofBits 0x4090000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FB1000000000000 : ℚ) : ℝ) ∧ (-(11 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(5) : ℝ) ∧ r = (418, 19, 6, Float.ofBits 0x4090000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC1300000000000 : ℚ) : ℝ) ∧ (-(6) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(11 / 2) : ℝ) ∧ r = (459, 24, 6, Float.ofBits 0x40B0000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC1500000000000 : ℚ) : ℝ) ∧ (-(13 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(6) : ℝ) ∧ r = (510, 24, 6, Float.ofBits 0x40B0000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC3400000000000 : ℚ) : ℝ) ∧ (-(7) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(13 / 2) : ℝ) ∧ r = (561, 25, 6, Float.ofBits 0x40D0000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC1450000000000 : ℚ) : ℝ) ∧ (-(15 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(7) : ℝ) ∧ r = (614, 24, 6, Float.ofBits 0x40E0000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(8) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(15 / 2) : ℝ) ∧ r = (665, 27, 6, Float.ofBits 0x4100000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ) ∧ (-(17 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(8) : ℝ) ∧ r = (722, 27, 6, Float.ofBits 0x4100000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) ∧ (-(9) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(17 / 2) : ℝ) ∧ r = (779, 28, 6, Float.ofBits 0x4130000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) ∧ (-(19 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(9) : ℝ) ∧ r = (838, 28, 6, Float.ofBits 0x4130000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(10) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(19 / 2) : ℝ) ∧ r = (897, 27, 6, Float.ofBits 0x4170000000000000)) ∨
    (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(21 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(10) : ℝ) ∧ r = (954, 27, 6, Float.ofBits 0x4170000000000000)) ∨
    (r = (0, 0, 0, 0.0) ∧ ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FB7400000000000 : ℚ) : ℝ) ∧ ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FB1680000000000 : ℚ) : ℝ) ∧ (-(3) : ℝ) < value sx.toBits ∧ value sx.toBits < ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ) ∧ (-(7 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(3) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ) ∧ (-(4) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(7 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC0000000000000 : ℚ) : ℝ) ∧ (-(9 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(4) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FB0800000000000 : ℚ) : ℝ) ∧ (-(5) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(9 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FB1000000000000 : ℚ) : ℝ) ∧ (-(11 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(5) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC1300000000000 : ℚ) : ℝ) ∧ (-(6) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(11 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC1500000000000 : ℚ) : ℝ) ∧ (-(13 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(6) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC3400000000000 : ℚ) : ℝ) ∧ (-(7) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(13 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC1450000000000 : ℚ) : ℝ) ∧ (-(15 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(7) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(8) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(15 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ) ∧ (-(17 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(8) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) ∧ (-(9) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(17 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) ∧ (-(19 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(9) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(10) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(19 / 2) : ℝ)) ∧
      ¬(value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(21 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(10) : ℝ))) := by
  unfold Lgamma.rootRange at hr
  dsimp only at hr
  have c0 : ((decide (afh < Float.ofBits 0x3FB7400000000000) && decide (sx > Float.ofBits 0xC004E147AE147AE1)) && decide (sx < (-2.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FB7400000000000 : ℚ) : ℝ) ∧ ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ sxb.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m2_0.1,
      TgammaWords.ofBits_value _ (by decide), sxb.2, m2_0.2]
    exact and_assoc
  have c1 : ((decide (afh < Float.ofBits 0x3FB1680000000000) && decide (sx > (-3.0 : Float))) && decide (sx < Float.ofBits 0xC004E147AE147AE1)) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FB1680000000000 : ℚ) : ℝ) ∧ (-(3) : ℝ) < value sx.toBits ∧ value sx.toBits < ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m3_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx sxb.1,
      TgammaWords.ofBits_value _ (by decide), m3_0.2, sxb.2]
    exact and_assoc
  have c2 : ((decide (afh < Float.ofBits 0x3FB2D40000000000) && decide (sx > (-3.5 : Float))) && decide (sx < (-3.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ) ∧ (-(7 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(3) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m3_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m3_0.1,
      TgammaWords.ofBits_value _ (by decide), m3_5.2, m3_0.2]
    exact and_assoc
  have c3 : ((decide (afh < Float.ofBits 0x3FAEF00000000000) && decide (sx > (-4.0 : Float))) && decide (sx < (-3.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ) ∧ (-(4) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(7 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m4_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m3_5.1,
      TgammaWords.ofBits_value _ (by decide), m4_0.2, m3_5.2]
    exact and_assoc
  have c4 : ((decide (afh < Float.ofBits 0x3FC0000000000000) && decide (sx > (-4.5 : Float))) && decide (sx < (-4.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC0000000000000 : ℚ) : ℝ) ∧ (-(9 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(4) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m4_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m4_0.1,
      TgammaWords.ofBits_value _ (by decide), m4_5.2, m4_0.2]
    exact and_assoc
  have c5 : ((decide (afh < Float.ofBits 0x3FB0800000000000) && decide (sx > (-5.0 : Float))) && decide (sx < (-4.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FB0800000000000 : ℚ) : ℝ) ∧ (-(5) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(9 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m5_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m4_5.1,
      TgammaWords.ofBits_value _ (by decide), m5_0.2, m4_5.2]
    exact and_assoc
  have c6 : ((decide (afh < Float.ofBits 0x3FB1000000000000) && decide (sx > (-5.5 : Float))) && decide (sx < (-5.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FB1000000000000 : ℚ) : ℝ) ∧ (-(11 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(5) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m5_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m5_0.1,
      TgammaWords.ofBits_value _ (by decide), m5_5.2, m5_0.2]
    exact and_assoc
  have c7 : ((decide (afh < Float.ofBits 0x3FC1300000000000) && decide (sx > (-6.0 : Float))) && decide (sx < (-5.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC1300000000000 : ℚ) : ℝ) ∧ (-(6) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(11 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m6_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m5_5.1,
      TgammaWords.ofBits_value _ (by decide), m6_0.2, m5_5.2]
    exact and_assoc
  have c8 : ((decide (afh < Float.ofBits 0x3FC1500000000000) && decide (sx > (-6.5 : Float))) && decide (sx < (-6.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC1500000000000 : ℚ) : ℝ) ∧ (-(13 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(6) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m6_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m6_0.1,
      TgammaWords.ofBits_value _ (by decide), m6_5.2, m6_0.2]
    exact and_assoc
  have c9 : ((decide (afh < Float.ofBits 0x3FC3400000000000) && decide (sx > (-7.0 : Float))) && decide (sx < (-6.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC3400000000000 : ℚ) : ℝ) ∧ (-(7) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(13 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m7_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m6_5.1,
      TgammaWords.ofBits_value _ (by decide), m7_0.2, m6_5.2]
    exact and_assoc
  have c10 : ((decide (afh < Float.ofBits 0x3FC1450000000000) && decide (sx > (-7.5 : Float))) && decide (sx < (-7.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC1450000000000 : ℚ) : ℝ) ∧ (-(15 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(7) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m7_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m7_0.1,
      TgammaWords.ofBits_value _ (by decide), m7_5.2, m7_0.2]
    exact and_assoc
  have c11 : ((decide (afh < Float.ofBits 0x3FC76B0000000000) && decide (sx > (-8.0 : Float))) && decide (sx < (-7.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(8) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(15 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m8_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m7_5.1,
      TgammaWords.ofBits_value _ (by decide), m8_0.2, m7_5.2]
    exact and_assoc
  have c12 : ((decide (afh < Float.ofBits 0x3FC76C0000000000) && decide (sx > (-8.5 : Float))) && decide (sx < (-8.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ) ∧ (-(17 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(8) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m8_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m8_0.1,
      TgammaWords.ofBits_value _ (by decide), m8_5.2, m8_0.2]
    exact and_assoc
  have c13 : ((decide (afh < Float.ofBits 0x3FC9900000000000) && decide (sx > (-9.0 : Float))) && decide (sx < (-8.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) ∧ (-(9) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(17 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m9_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m8_5.1,
      TgammaWords.ofBits_value _ (by decide), m9_0.2, m8_5.2]
    exact and_assoc
  have c14 : ((decide (afh < Float.ofBits 0x3FC9900000000000) && decide (sx > (-9.5 : Float))) && decide (sx < (-9.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) ∧ (-(19 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(9) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m9_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m9_0.1,
      TgammaWords.ofBits_value _ (by decide), m9_5.2, m9_0.2]
    exact and_assoc
  have c15 : ((decide (afh < Float.ofBits 0x3FC76B0000000000) && decide (sx > (-10.0 : Float))) && decide (sx < (-9.5 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(10) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(19 / 2) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m10_0.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m9_5.1,
      TgammaWords.ofBits_value _ (by decide), m10_0.2, m9_5.2]
    exact and_assoc
  have c16 : ((decide (afh < Float.ofBits 0x3FC76B0000000000) && decide (sx > (-10.5 : Float))) && decide (sx < (-10.0 : Float))) = true ↔
      (value afh.toBits < ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) ∧ (-(21 / 2) : ℝ) < value sx.toBits ∧ value sx.toBits < (-(10) : ℝ)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
    rw [F64UpperWord.float_lt_iff _ _ haf (TgammaWords.ofBits_finite _ (by decide)),
      F64UpperWord.float_lt_iff _ _ m10_5.1 hsx, F64UpperWord.float_lt_iff _ _ hsx m10_0.1,
      TgammaWords.ofBits_value _ (by decide), m10_5.2, m10_0.2]
    exact and_assoc
  by_cases h0 : ((decide (afh < Float.ofBits 0x3FB7400000000000) && decide (sx > Float.ofBits 0xC004E147AE147AE1)) && decide (sx < (-2.0 : Float))) = true
  · rw [if_pos h0] at hr
    exact Or.inl ⟨(c0.mp h0).1, (c0.mp h0).2.1, (c0.mp h0).2.2, hr.symm⟩
  rw [if_neg h0] at hr
  by_cases h1 : ((decide (afh < Float.ofBits 0x3FB1680000000000) && decide (sx > (-3.0 : Float))) && decide (sx < Float.ofBits 0xC004E147AE147AE1)) = true
  · rw [if_pos h1] at hr
    exact Or.inr (Or.inl ⟨(c1.mp h1).1, (c1.mp h1).2.1, (c1.mp h1).2.2, hr.symm⟩)
  rw [if_neg h1] at hr
  by_cases h2 : ((decide (afh < Float.ofBits 0x3FB2D40000000000) && decide (sx > (-3.5 : Float))) && decide (sx < (-3.0 : Float))) = true
  · rw [if_pos h2] at hr
    exact Or.inr (Or.inr (Or.inl ⟨(c2.mp h2).1, (c2.mp h2).2.1, (c2.mp h2).2.2, hr.symm⟩))
  rw [if_neg h2] at hr
  by_cases h3 : ((decide (afh < Float.ofBits 0x3FAEF00000000000) && decide (sx > (-4.0 : Float))) && decide (sx < (-3.5 : Float))) = true
  · rw [if_pos h3] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(c3.mp h3).1, (c3.mp h3).2.1, (c3.mp h3).2.2, hr.symm⟩)))
  rw [if_neg h3] at hr
  by_cases h4 : ((decide (afh < Float.ofBits 0x3FC0000000000000) && decide (sx > (-4.5 : Float))) && decide (sx < (-4.0 : Float))) = true
  · rw [if_pos h4] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c4.mp h4).1, (c4.mp h4).2.1, (c4.mp h4).2.2, hr.symm⟩))))
  rw [if_neg h4] at hr
  by_cases h5 : ((decide (afh < Float.ofBits 0x3FB0800000000000) && decide (sx > (-5.0 : Float))) && decide (sx < (-4.5 : Float))) = true
  · rw [if_pos h5] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c5.mp h5).1, (c5.mp h5).2.1, (c5.mp h5).2.2, hr.symm⟩)))))
  rw [if_neg h5] at hr
  by_cases h6 : ((decide (afh < Float.ofBits 0x3FB1000000000000) && decide (sx > (-5.5 : Float))) && decide (sx < (-5.0 : Float))) = true
  · rw [if_pos h6] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c6.mp h6).1, (c6.mp h6).2.1, (c6.mp h6).2.2, hr.symm⟩))))))
  rw [if_neg h6] at hr
  by_cases h7 : ((decide (afh < Float.ofBits 0x3FC1300000000000) && decide (sx > (-6.0 : Float))) && decide (sx < (-5.5 : Float))) = true
  · rw [if_pos h7] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c7.mp h7).1, (c7.mp h7).2.1, (c7.mp h7).2.2, hr.symm⟩)))))))
  rw [if_neg h7] at hr
  by_cases h8 : ((decide (afh < Float.ofBits 0x3FC1500000000000) && decide (sx > (-6.5 : Float))) && decide (sx < (-6.0 : Float))) = true
  · rw [if_pos h8] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c8.mp h8).1, (c8.mp h8).2.1, (c8.mp h8).2.2, hr.symm⟩))))))))
  rw [if_neg h8] at hr
  by_cases h9 : ((decide (afh < Float.ofBits 0x3FC3400000000000) && decide (sx > (-7.0 : Float))) && decide (sx < (-6.5 : Float))) = true
  · rw [if_pos h9] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c9.mp h9).1, (c9.mp h9).2.1, (c9.mp h9).2.2, hr.symm⟩)))))))))
  rw [if_neg h9] at hr
  by_cases h10 : ((decide (afh < Float.ofBits 0x3FC1450000000000) && decide (sx > (-7.5 : Float))) && decide (sx < (-7.0 : Float))) = true
  · rw [if_pos h10] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c10.mp h10).1, (c10.mp h10).2.1, (c10.mp h10).2.2, hr.symm⟩))))))))))
  rw [if_neg h10] at hr
  by_cases h11 : ((decide (afh < Float.ofBits 0x3FC76B0000000000) && decide (sx > (-8.0 : Float))) && decide (sx < (-7.5 : Float))) = true
  · rw [if_pos h11] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c11.mp h11).1, (c11.mp h11).2.1, (c11.mp h11).2.2, hr.symm⟩)))))))))))
  rw [if_neg h11] at hr
  by_cases h12 : ((decide (afh < Float.ofBits 0x3FC76C0000000000) && decide (sx > (-8.5 : Float))) && decide (sx < (-8.0 : Float))) = true
  · rw [if_pos h12] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c12.mp h12).1, (c12.mp h12).2.1, (c12.mp h12).2.2, hr.symm⟩))))))))))))
  rw [if_neg h12] at hr
  by_cases h13 : ((decide (afh < Float.ofBits 0x3FC9900000000000) && decide (sx > (-9.0 : Float))) && decide (sx < (-8.5 : Float))) = true
  · rw [if_pos h13] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c13.mp h13).1, (c13.mp h13).2.1, (c13.mp h13).2.2, hr.symm⟩)))))))))))))
  rw [if_neg h13] at hr
  by_cases h14 : ((decide (afh < Float.ofBits 0x3FC9900000000000) && decide (sx > (-9.5 : Float))) && decide (sx < (-9.0 : Float))) = true
  · rw [if_pos h14] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c14.mp h14).1, (c14.mp h14).2.1, (c14.mp h14).2.2, hr.symm⟩))))))))))))))
  rw [if_neg h14] at hr
  by_cases h15 : ((decide (afh < Float.ofBits 0x3FC76B0000000000) && decide (sx > (-10.0 : Float))) && decide (sx < (-9.5 : Float))) = true
  · rw [if_pos h15] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c15.mp h15).1, (c15.mp h15).2.1, (c15.mp h15).2.2, hr.symm⟩)))))))))))))))
  rw [if_neg h15] at hr
  by_cases h16 : ((decide (afh < Float.ofBits 0x3FC76B0000000000) && decide (sx > (-10.5 : Float))) && decide (sx < (-10.0 : Float))) = true
  · rw [if_pos h16] at hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(c16.mp h16).1, (c16.mp h16).2.1, (c16.mp h16).2.2, hr.symm⟩))))))))))))))))
  rw [if_neg h16] at hr
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hr.symm, fun h => h0 (c0.mpr h), fun h => h1 (c1.mpr h), fun h => h2 (c2.mpr h), fun h => h3 (c3.mpr h), fun h => h4 (c4.mpr h), fun h => h5 (c5.mpr h), fun h => h6 (c6.mpr h), fun h => h7 (c7.mpr h), fun h => h8 (c8.mpr h), fun h => h9 (c9.mpr h), fun h => h10 (c10.mpr h), fun h => h11 (c11.mpr h), fun h => h12 (c12.mpr h), fun h => h13 (c13.mpr h), fun h => h14 (c14.mpr h), fun h => h15 (c15.mpr h), fun h => h16 (c16.mpr h)⟩))))))))))))))))

end Verified.Examples.LgammaRootSel
