import Verified.Examples.AtanTwoBranches
import LeanExe.ProofKit.F64DivBounds
import LeanExe.ProofKit.F64RoundDouble

/-!
The argument `q = |y/x|` of `atan` in `Atan.atan2`: a finite word within `2 ^ -53 Q + 2 ^ -1075`
of `Q = |y/x|`, and the change of `arctan` between `q` and `Q`.
-/

namespace Verified.Examples.AtanTwoQuot
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem quot_facts (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits)
    (hx0 : value x.toBits ≠ 0) (hQ : |value y.toBits / value x.toBits| < 2 ^ 1022) :
    Finite (y / x).abs.toBits ∧
      |value (y / x).abs.toBits - (|value y.toBits / value x.toBits|)| ≤
        |value y.toBits / value x.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
  have hm := F64RoundDouble.mag_pos x.toBits hx0
  obtain ⟨hdf, hde⟩ := F64DivBounds.div_real_mixed y.toBits x.toBits hy hx hm.ne' hQ
  rw [← F64Bits.toBits_div] at hdf hde
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts (y / x) hdf
  refine ⟨haf, ?_⟩
  rw [hav]
  have h1 := abs_abs_sub_abs_le_abs_sub (value (y / x).toBits) (value y.toBits / value x.toBits)
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have he : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  rw [hu, he] at hde
  have h2 : 1 / 2 ^ 53 * |value y.toBits / value x.toBits| =
      |value y.toBits / value x.toBits| / 2 ^ 53 := by ring
  linarith

/-- `arctan b - arctan a ≤ (b - a)/(1 + m²)` for `0 ≤ m ≤ a ≤ b`. -/
theorem arctan_sub_le (a b m : ℝ) (hm : 0 ≤ m) (ha : m ≤ a) (hab : a ≤ b) :
    Real.arctan b - Real.arctan a ≤ (b - a) / (1 + m ^ 2) := by
  have hsum := Real.arctan_add (x := b) (y := -a) (by nlinarith)
  rw [Real.arctan_neg, ← sub_eq_add_neg] at hsum
  have hden : 0 < 1 + b * a := by nlinarith
  rw [hsum, show (b + -a) / (1 - b * -a) = (b - a) / (1 + b * a) by ring]
  calc Real.arctan ((b - a) / (1 + b * a)) ≤ max ((b - a) / (1 + b * a)) 0 :=
        AtanTheoremCases.arctan_le_max _
    _ = (b - a) / (1 + b * a) := max_eq_left (div_nonneg (by linarith) hden.le)
    _ ≤ (b - a) / (1 + m ^ 2) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith)

/-- `arctan` moves by at most `|q - Q|/(1 + m²)` between `q` and `Q`, both at least `m ≥ 0`. -/
theorem arctan_diff (q Q m : ℝ) (hm : 0 ≤ m) (hq : m ≤ q) (hQ : m ≤ Q) :
    |Real.arctan q - Real.arctan Q| ≤ |q - Q| / (1 + m ^ 2) := by
  rcases le_total q Q with h | h
  · rw [abs_of_nonpos (by linarith [Real.arctan_mono h]), abs_of_nonpos (by linarith)]
    have := arctan_sub_le q Q m hm hq h
    rw [show -(q - Q) = Q - q by ring]
    linarith
  · rw [abs_of_nonneg (by linarith [Real.arctan_mono h]), abs_of_nonneg (by linarith)]
    exact arctan_sub_le Q q m hm hQ h

#print axioms quot_facts
#print axioms arctan_diff

end Verified.Examples.AtanTwoQuot
