import Library.Numerics.Float64.Bessel.BesselY0Large
import Library.Numerics.Float64.Bessel.BesselY0Small

/-!
The accuracy theorem for `Bessel.y0`: for every finite `x > 0`, the result lies within
`11 · 2^-53 · √(J₀(x)² + Y₀(x)²)` of `Y₀(x)` (`y0_accuracy`).  From 2 on,
`BesselY0Large.y0_large` gives the bound with 10 in place of 11; below 2,
`BesselY0Small.y0_small` gives it.  The exceptional results, at both zeros, at negative arguments,
and at the infinities and NaN, are in `BesselSpecial`.
-/

namespace Library.Numerics.Float64.Bessel.BesselY0Theorem
open CodeLib.IEEE64 LeanExe.ProofKit BesselY0Large BesselY0Small
open LeanExe.ProofKit.Bessel (J0 Y0)

local notation "𝐮" => unitRoundoff64

/-- `y0` for every finite `x > 0`. -/
theorem y0_accuracy (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) :
    |value (Bessel.y0 x).toBits - Y0 (value x.toBits)| ≤
      11 / 2 ^ 53 * √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have e : (11 : ℝ) / 2 ^ 53 = 11 * 𝐮 := by rw [hu]; ring
  rw [e]
  by_cases h2 : 0x4000000000000000 ≤ x.toBits.toNat
  · have h := y0_large x hxf hpos h2
    have hm : 0 ≤ 𝐮 * √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2) := by
      rw [hu]; positivity
    nlinarith
  · push Not at h2
    exact y0_small x hxf hpos hnz h2

#print axioms y0_accuracy

end Library.Numerics.Float64.Bessel.BesselY0Theorem
