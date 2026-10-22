import Library.Numerics.Float64.Bessel.BesselJ1Large
import Library.Numerics.Float64.Bessel.BesselJ1Small
import Library.Numerics.Float64.Bessel.BesselModSmall1

/-!
The accuracy theorem for `Bessel.j1`: for every finite `x`, the result lies within
`12 · 2^-53 · √(J₁(|x|)² + Y₁(|x|)²)` of `J₁(x)` (`j1_accuracy`).  From `|x| = 2` on,
`BesselJ1Large.j1_large` gives the bound.  Below 2 and away from zero, `BesselJ1Small.j1_small`
bounds the error by `3.89 · 2^-53` and `BesselModSmall1.modulus1_lower` bounds the modulus below
by `0.42`.  At both zeros the result has the value 0 (`BesselJ1Small.j1_zero`), as `J₁(0)` does.
The exceptional results are in `BesselSpecial`.
-/

namespace Library.Numerics.Float64.Bessel.BesselJ1Theorem
open CodeLib.IEEE64 LeanExe.ProofKit BesselJ1Large BesselJ1Small BesselModSmall1
open LeanExe.ProofKit.Bessel (J1 Y1)

local notation "𝐮" => unitRoundoff64

/-- `j1` for every finite `x`. -/
theorem j1_accuracy (x : Float) (hxf : Finite x.toBits) :
    |value (Bessel.j1 x).toBits - J1 (value x.toBits)| ≤
      12 / 2 ^ 53 * √(J1 |value x.toBits| ^ 2 + Y1 |value x.toBits| ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ 𝐮 := by rw [hu]; positivity
  have e : (12 : ℝ) / 2 ^ 53 = 12 * 𝐮 := by rw [hu]; ring
  rw [e]
  by_cases h2 : 0x4000000000000000 ≤ x.toBits.toNat % 2 ^ 63
  · exact j1_large x hxf h2
  push Not at h2
  by_cases hz : x.toBits.toNat % 2 ^ 63 = 0
  · obtain ⟨hv, hj⟩ := j1_zero x hz
    have h0 : J1 0 = 0 := by simp [LeanExe.ProofKit.Bessel.J1]
    rw [hj, hv, h0, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hu0) (Real.sqrt_nonneg _)
  have hs := (j1_small x hxf h2).2
  have hab := F64Bits.toBits_abs x
  have hN := Library.Numerics.Float64.Trig.TrigSinCos.abs_toNat x.toBits
  have hav : value x.abs.toBits = |value x.toBits| := by rw [hab, Library.Numerics.Float64.Trig.TrigSinCos.abs_value]
  have hlt : |value x.toBits| < 2 := by
    have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) (by
        rw [hab, hN]; simp only [UInt64.reduceToNat]; exact h2)
    rw [BesselJ0Large.value_two, hav] at h
    exact h
  have hpos : 0 < |value x.toBits| := by
    have h := F64PositiveOrder.value_strict (left := (0 : UInt64)) (right := x.abs.toBits)
      (by rw [hab, hN]; omega) (by rw [hab, hN]; simp only [UInt64.toNat_zero]; omega)
    rw [F64Magnitude.value_zero, hav] at h
    exact h
  have hM := modulus1_lower |value x.toBits| hpos hlt.le
  have hE := j1Err_le |value x.toBits|
  calc |value (Bessel.j1 x).toBits - J1 (value x.toBits)| ≤ 389 / 100 * 𝐮 := hs.trans hE
    _ ≤ 12 * 𝐮 * (42 / 100) := by nlinarith
    _ ≤ 12 * 𝐮 * √(J1 |value x.toBits| ^ 2 + Y1 |value x.toBits| ^ 2) :=
        mul_le_mul_of_nonneg_left hM (by positivity)

#print axioms j1_accuracy

end Library.Numerics.Float64.Bessel.BesselJ1Theorem
