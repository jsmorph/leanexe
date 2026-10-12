import Verified.Examples.BesselJ0Large
import Verified.Examples.BesselJ0Small
import Verified.Examples.BesselModSmall

/-!
The accuracy theorem for `Bessel.j0`: for every finite `x`, the result lies within
`10 · 2^-53 · √(J₀(|x|)² + Y₀(|x|)²)` of `J₀(x)` (`j0_accuracy`).  From `|x| = 2` on,
`BesselJ0Large.j0_large` gives the bound; below 2, `BesselJ0Small.j0_small` bounds the error by
`(235/100) 2^-53` and `BesselModSmall.modulus0_half` the modulus below by `1/2`.  The exceptional
results are in `BesselSpecial`.
-/

namespace Verified.Examples.BesselJ0Theorem
open CodeLib.IEEE64 LeanExe.ProofKit BesselJ0Large BesselJ0Small BesselModSmall
open LeanExe.ProofKit.Bessel (J0 Y0)

local notation "𝐮" => unitRoundoff64

/-- `j0` for every finite `x`. -/
theorem j0_accuracy (x : Float) (hxf : Finite x.toBits) :
    |value (Bessel.j0 x).toBits - J0 (value x.toBits)| ≤
      10 / 2 ^ 53 * √(J0 |value x.toBits| ^ 2 + Y0 |value x.toBits| ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have e : (10 : ℝ) / 2 ^ 53 = 10 * 𝐮 := by rw [hu]; ring
  rw [e]
  by_cases h2 : 0x4000000000000000 ≤ x.toBits.toNat % 2 ^ 63
  · exact j0_large x hxf h2
  · push Not at h2
    have hs := (j0_small x hxf h2).2
    have hab := F64Bits.toBits_abs x
    have hN := TrigSinCos.abs_toNat x.toBits
    have hav : value x.abs.toBits = |value x.toBits| := by rw [hab, TrigSinCos.abs_value]
    have hlt : |value x.toBits| < 2 := by
      have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
        (right := (0x4000000000000000 : UInt64)) (by decide) (by
          rw [hab, hN]; simp only [UInt64.reduceToNat]; exact h2)
      rw [value_two, hav] at h
      exact h
    have hM := modulus0_half |value x.toBits| (abs_nonneg _) hlt.le
    have hu0 : 0 ≤ 𝐮 := by rw [hu]; positivity
    calc |value (Bessel.j0 x).toBits - J0 (value x.toBits)| ≤ 235 / 100 * 𝐮 := hs
      _ ≤ 10 * 𝐮 * (1 / 2) := by nlinarith
      _ ≤ 10 * 𝐮 * √(J0 |value x.toBits| ^ 2 + Y0 |value x.toBits| ^ 2) :=
          mul_le_mul_of_nonneg_left hM (by positivity)

#print axioms j0_accuracy

end Verified.Examples.BesselJ0Theorem
