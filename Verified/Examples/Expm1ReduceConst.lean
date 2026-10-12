import Verified.Examples.ExpReductionBounds
import Verified.Examples.Expm1FormBase

/-!
The constants of the reduction in fdlibm's `expm1`: `ln2Hi`, `ln2Lo`, and `invln2`, and the
high-word thresholds as values.  `ln2Hi + ln2Lo` lies within `2 ^ -86` of `log 2`, and
`invln2 · log 2` within `2 ^ -55` of 1, both from `ExpReductionBounds.log_two_enclosure`.
-/

namespace Verified.Examples.Expm1ReduceConst
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

def ln2Hi : UInt64 := 0x3FE62E42FEE00000
def ln2Lo : UInt64 := 0x3DEA39EF35793C76
def invln2 : UInt64 := 0x3FF71547652B82FE

theorem const_finite : Finite ln2Hi ∧ Finite ln2Lo ∧ Finite invln2 := by
  unfold CodeLib.IEEE64.Finite ln2Hi ln2Lo invln2
  decide +kernel

theorem split_check :
    PolyBound.qabs (ExpReductionBounds.splitLogTwo - PolyBound.ratOfWord ln2Hi -
        PolyBound.ratOfWord ln2Lo) + 1 / 2 ^ 92 ≤ 1 / 2 ^ 86 ∧
      PolyBound.qabs (PolyBound.ratOfWord invln2 * ExpReductionBounds.splitLogTwo - 1) +
        PolyBound.ratOfWord invln2 / 2 ^ 92 ≤ 1 / 2 ^ 55 ∧
      0 < PolyBound.ratOfWord invln2 := by
  decide +kernel

/-- The enclosure of `log 2` around `splitLogTwo`. -/
theorem log_two_near : |Real.log 2 - ((ExpReductionBounds.splitLogTwo : ℚ) : ℝ)| ≤ 1 / 2 ^ 92 := by
  obtain ⟨hl, hu⟩ := ExpReductionBounds.log_two_enclosure
  simp only [ExpReductionBounds.lowerLogTwo, ExpReductionBounds.upperLogTwo, Rat.cast_sub,
    Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at hl hu
  rw [abs_le]; constructor <;> linarith

/-- `ln2Hi + ln2Lo` against `log 2`. -/
theorem ln2_split : |Real.log 2 - value ln2Hi - value ln2Lo| ≤ 1 / 2 ^ 86 := by
  obtain ⟨h1, -, -⟩ := split_check
  have h1' := (Rat.cast_le (K := ℝ)).mpr h1
  push_cast [PolyBound.qabs_cast, PolyBound.ratOfWord_cast] at h1'
  have hd := log_two_near
  set S := ((ExpReductionBounds.splitLogTwo : ℚ) : ℝ)
  calc |Real.log 2 - value ln2Hi - value ln2Lo| =
      |(Real.log 2 - S) + (S - value ln2Hi - value ln2Lo)| := by ring_nf
    _ ≤ |Real.log 2 - S| + |S - value ln2Hi - value ln2Lo| := abs_add_le _ _
    _ ≤ 1 / 2 ^ 86 := by linarith

/-- `invln2 · log 2` against 1. -/
theorem invln2_bound : |value invln2 * Real.log 2 - 1| ≤ 1 / 2 ^ 55 := by
  obtain ⟨-, h2, hpos⟩ := split_check
  have h2' := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast [PolyBound.qabs_cast, PolyBound.ratOfWord_cast] at h2'
  have hpos' : (0 : ℝ) < value invln2 := by
    rw [← PolyBound.ratOfWord_cast]; exact_mod_cast hpos
  have hd := log_two_near
  set S := ((ExpReductionBounds.splitLogTwo : ℚ) : ℝ)
  have hm : |value invln2 * Real.log 2 - value invln2 * S| ≤ value invln2 * (1 / 2 ^ 92) := by
    rw [← mul_sub, abs_mul, abs_of_pos hpos']
    exact mul_le_mul_of_nonneg_left hd hpos'.le
  calc |value invln2 * Real.log 2 - 1| ≤ |value invln2 * Real.log 2 - value invln2 * S| +
      |value invln2 * S - 1| := abs_sub_le _ _ _
    _ ≤ 1 / 2 ^ 55 := by
        have : value invln2 * (1 / 2 ^ 92) = value invln2 / 2 ^ 92 := by ring
        linarith

#print axioms ln2_split
#print axioms invln2_bound

end Verified.Examples.Expm1ReduceConst
