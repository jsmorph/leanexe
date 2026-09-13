import Project.ProofKit.F64Packing

namespace Project.ProofKit.F64AddBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem add_scaled_relative (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs < 2^2097) :
    Finite (Wasm.IEEE64.add a b) ∧
    |Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) -
      (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b)| * (2^53 : Int) ≤
      (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  by_cases hz : z = 0
  · exact CodeLib.IEEE64.add_relative_spec a b ha hb (by change z.natAbs < 2^1076; simp [hz])
  · have hround := F64Packing.signed_pack_relative z hbound
    simpa [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz] using hround

theorem add_real_relative (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a + value b| < (2 : ℝ)^1023) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
      unitRoundoff64 * |value a + value b| := by
  let exactScaled := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  let errorScaled := Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) - exactScaled
  have hscalePos : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hexactEq : value a + value b = (exactScaled : ℝ) / (2 : ℝ)^1074 := by
    simp [value, exactScaled]
    ring
  have hscaledBound : exactScaled.natAbs < 2^2097 := by
    rw [hexactEq, abs_div, abs_of_pos hscalePos] at hbound
    have hs := (div_lt_iff₀ hscalePos).mp hbound
    rw [← pow_add] at hs
    have hi : |exactScaled| < (2^2097 : Int) := by exact_mod_cast hs
    exact natAbs_lt_nat hi
  have hs := add_scaled_relative a b ha hb hscaledBound
  refine ⟨hs.1, ?_⟩
  have hscaled : |errorScaled| * (2^53 : Int) ≤ exactScaled.natAbs := hs.2
  have hscaledReal : |(errorScaled : ℝ)| * (2 : ℝ)^53 ≤ |(exactScaled : ℝ)| := by
    exact_mod_cast hscaled
  have hunit : |(errorScaled : ℝ)| ≤ |(exactScaled : ℝ)| / (2 : ℝ)^53 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^53)).2 hscaledReal
  have herrorEq : value (Wasm.IEEE64.add a b) - (value a + value b) =
      (errorScaled : ℝ) / (2 : ℝ)^1074 := by
    simp [value, errorScaled, exactScaled]
    ring
  rw [herrorEq, abs_div, abs_of_pos hscalePos, hexactEq, abs_div, abs_of_pos hscalePos]
  calc
    |(errorScaled : ℝ)| / (2 : ℝ)^1074 ≤
        (|(exactScaled : ℝ)| / (2 : ℝ)^53) / (2 : ℝ)^1074 :=
      div_le_div_of_nonneg_right hunit hscalePos.le
    _ = unitRoundoff64 * (|(exactScaled : ℝ)| / (2 : ℝ)^1074) := by
      simp [unitRoundoff64]
      ring

theorem sub_real_relative (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a - value b| < (2 : ℝ)^1023) :
    Finite (Wasm.IEEE64.sub a b) ∧
    |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤
      unitRoundoff64 * |value a - value b| := by
  have hn := negate_spec b hb
  have hv : value (Wasm.IEEE64.negate b) = -value b := by
    simp [value, hn.2]
    ring
  have hs := add_real_relative a (Wasm.IEEE64.negate b) ha hn.1
    (by simpa only [hv, ← sub_eq_add_neg] using hbound)
  simpa only [Wasm.IEEE64.sub, hv, ← sub_eq_add_neg] using hs

#print axioms add_scaled_relative
#print axioms add_real_relative
#print axioms sub_real_relative
end Project.ProofKit.F64AddBounds
