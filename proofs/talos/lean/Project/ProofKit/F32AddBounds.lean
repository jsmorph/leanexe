import Project.ProofKit.F32Packing

namespace Project.ProofKit.F32AddBounds
open CodeLib.IEEE32

set_option exponentiation.threshold 512

noncomputable def unitRoundoff : ℝ := 1 / (2:ℝ)^24

theorem add_scaled_relative (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs < 2^276) :
    Finite (Wasm.IEEE32.add a b) ∧
    |Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) -
      (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b)| * (2^24 : Int) ≤
      (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs := by
  let z := Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b
  by_cases hz : z = 0
  · have hzero : Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) = 0 := by
      simp [Wasm.IEEE32.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz]
      split <;> norm_num [Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
    have hfinite := (CodeLib.IEEE32.add_spec a b ha hb
      (by change z.natAbs < 2^151; simp [hz])).1
    exact ⟨hfinite, by change |Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) - z| * _ ≤ _; simp [hzero, hz]⟩
  · have hround := F32Packing.signed_pack_relative z hbound
    simpa [Wasm.IEEE32.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz] using hround

theorem add_real_relative (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : |value a + value b| < (2 : ℝ)^127) :
    Finite (Wasm.IEEE32.add a b) ∧
    |value (Wasm.IEEE32.add a b) - (value a + value b)| ≤
      unitRoundoff * |value a + value b| := by
  let exactScaled := Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b
  let errorScaled := Wasm.IEEE32.scaledValue (Wasm.IEEE32.add a b) - exactScaled
  have hscalePos : (0 : ℝ) < (2 : ℝ)^149 := by positivity
  have hexactEq : value a + value b = (exactScaled : ℝ) / (2 : ℝ)^149 := by
    simp [value, exactScaled]
    ring
  have hscaledBound : exactScaled.natAbs < 2^276 := by
    rw [hexactEq, abs_div, abs_of_pos hscalePos] at hbound
    have hs := (div_lt_iff₀ hscalePos).mp hbound
    rw [← pow_add] at hs
    have hi : |exactScaled| < (2^276 : Int) := by exact_mod_cast hs
    exact natAbs_lt_nat hi
  have hs := add_scaled_relative a b ha hb hscaledBound
  refine ⟨hs.1, ?_⟩
  have hscaled : |errorScaled| * (2^24 : Int) ≤ exactScaled.natAbs := hs.2
  have hscaledReal : |(errorScaled : ℝ)| * (2 : ℝ)^24 ≤ |(exactScaled : ℝ)| := by
    exact_mod_cast hscaled
  have hunit : |(errorScaled : ℝ)| ≤ |(exactScaled : ℝ)| / (2 : ℝ)^24 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^24)).2 hscaledReal
  have herrorEq : value (Wasm.IEEE32.add a b) - (value a + value b) =
      (errorScaled : ℝ) / (2 : ℝ)^149 := by
    simp [value, errorScaled, exactScaled]
    ring
  rw [herrorEq, abs_div, abs_of_pos hscalePos, hexactEq, abs_div, abs_of_pos hscalePos]
  calc
    |(errorScaled : ℝ)| / (2 : ℝ)^149 ≤
        (|(exactScaled : ℝ)| / (2 : ℝ)^24) / (2 : ℝ)^149 :=
      div_le_div_of_nonneg_right hunit hscalePos.le
    _ = unitRoundoff * (|(exactScaled : ℝ)| / (2 : ℝ)^149) := by
      simp [unitRoundoff]
      ring

theorem sub_real_relative (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : |value a - value b| < (2 : ℝ)^127) :
    Finite (Wasm.IEEE32.sub a b) ∧
    |value (Wasm.IEEE32.sub a b) - (value a - value b)| ≤
      unitRoundoff * |value a - value b| := by
  have hn := negate_spec b hb
  have hv : value (Wasm.IEEE32.negate b) = -value b := by
    simp [value, hn.2]
    ring
  have hs := add_real_relative a (Wasm.IEEE32.negate b) ha hn.1
    (by simpa only [hv, ← sub_eq_add_neg] using hbound)
  simpa only [Wasm.IEEE32.sub, hv, ← sub_eq_add_neg] using hs

#print axioms add_scaled_relative
#print axioms add_real_relative
#print axioms sub_real_relative
end Project.ProofKit.F32AddBounds
