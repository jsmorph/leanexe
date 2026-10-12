import Verified.Examples.BesselY1Large
import Verified.Examples.BesselY1Small
import Verified.Examples.BesselY1Tiny

/-!
The accuracy theorems for `Bessel.y1`.  For every finite `x ≥ 2^-1022`, the result lies within
`12 · 2^-53 · √(J₁(x)² + Y₁(x)²)` of `Y₁(x)` (`y1_accuracy`), from `BesselY1Large.y1_large` from 2
on and `BesselY1Small.y1_small` below.  For `0 < x` below the high word `0x3c900000`, about
`2^-54`, subnormal arguments included, the result lies within one representable step of the
nearest-even double to `Y₁(x)` (`BesselY1Tiny.y1_tiny`): there `Y₁(x)` is about `-2/(π x)`, which
exceeds the largest double below about `0.64 · 2^-1024`, where the result is negative infinity.
`y1_positive` joins the two statements, which together cover every finite `x > 0`.  The
exceptional results, at both zeros, at negative arguments, and at the infinities and NaN, are in
`BesselSpecial`.
-/

namespace Verified.Examples.BesselY1Theorem
open CodeLib.IEEE64 LeanExe.ProofKit BesselY1Large BesselY1Small BesselY1Tiny
open LeanExe.ProofKit.Bessel (J1 Y1)

local notation "𝐮" => unitRoundoff64

/-- `y1` for every finite `x ≥ 2^-1022`. -/
theorem y1_accuracy (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnorm : 0x0010000000000000 ≤ x.toBits.toNat) :
    |value (Bessel.y1 x).toBits - Y1 (value x.toBits)| ≤
      12 / 2 ^ 53 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have e : (12 : ℝ) / 2 ^ 53 = 12 * 𝐮 := by rw [hu]; ring
  rw [e]
  by_cases h2 : 0x4000000000000000 ≤ x.toBits.toNat
  · exact y1_large x hxf hpos h2
  · push Not at h2
    exact y1_small x hxf hpos hnorm h2

/-- `y1` for every finite `x > 0`: the modulus bound from `2^-1022` on, and one step below the
high word `0x3c900000`. -/
theorem y1_positive (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) :
    (0x0010000000000000 ≤ x.toBits.toNat →
      |value (Bessel.y1 x).toBits - Y1 (value x.toBits)| ≤
        12 / 2 ^ 53 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2)) ∧
    (x.toBits.toNat < 0x3C90000100000000 →
      F64SignedRounding.WithinSteps 1 (Y1 (value x.toBits)) (Bessel.y1 x).toBits) :=
  ⟨y1_accuracy x hxf hpos, y1_tiny x hxf hpos hnz⟩

#print axioms y1_accuracy
#print axioms y1_positive

end Verified.Examples.BesselY1Theorem
