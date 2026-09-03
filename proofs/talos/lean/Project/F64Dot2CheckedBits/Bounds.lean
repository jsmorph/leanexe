import CodeLib.Numerical.Kernels

/-!
# Raw binary64 bounds for the guarded two-term dot product

The LeanExe entry point checks a binary64 word after clearing its sign bit.
This module proves that the accepted raw-bit interval contains only finite
values whose real magnitude is at most one half.  The proof uses only the
integer IEEE-754 model; it does not evaluate native floating-point values.
-/

namespace Project.F64Dot2CheckedBits.Bounds

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- Clear the sign bit of a binary64 word, exactly as the LeanExe guard does. -/
def f64AbsBits (bits : UInt64) : UInt64 :=
  bits &&& 0x7FFFFFFFFFFFFFFF

/-- Proof-side copy of `LeanExe.Examples.Float64Bits.boundedByHalf`. -/
def boundedByHalfBits (bits : UInt64) : Bool :=
  decide (f64AbsBits bits ≤ 0x3FE0000000000000)

private theorem f64AbsBits_toNat (bits : UInt64) :
    (f64AbsBits bits).toNat = bits.toNat % 2 ^ 63 := by
  simp only [f64AbsBits, UInt64.toNat_and]
  change bits.toNat &&& (2 ^ 63 - 1) = bits.toNat % 2 ^ 63
  exact Nat.and_two_pow_sub_one_eq_mod bits.toNat 63

/-- Passing the source program's raw-bit guard implies both finiteness and the
real magnitude bound consumed by the binary64 numerical kernel theorems. -/
theorem boundedByHalf_spec (bits : UInt64)
    (hguard : boundedByHalfBits bits = true) :
    CodeLib.IEEE64.Finite bits ∧
      |CodeLib.IEEE64.value bits| ≤ (1 : ℝ) / 2 := by
  have hguard' : f64AbsBits bits ≤ 0x3FE0000000000000 := by
    simpa [boundedByHalfBits] using hguard
  let magnitudeBits := (f64AbsBits bits).toNat
  let exponentField := magnitudeBits / 2 ^ 52
  let fractionField := magnitudeBits % 2 ^ 52
  have hmagnitudeBits :
      magnitudeBits = bits.toNat % 2 ^ 63 :=
    f64AbsBits_toNat bits
  have hmagnitudeBound : magnitudeBits ≤ 1022 * 2 ^ 52 := by
    have h := UInt64.le_iff_toNat_le.mp hguard'
    change magnitudeBits ≤ 1022 * 2 ^ 52
    change (f64AbsBits bits).toNat ≤
      (0x3FE0000000000000 : UInt64).toNat at h
    norm_num at h ⊢
    exact h
  have hfractionLt : fractionField < 2 ^ 52 := by
    exact Nat.mod_lt _ (by positivity)
  have hmagnitudeDecomp :
      magnitudeBits = exponentField * 2 ^ 52 + fractionField := by
    dsimp [exponentField, fractionField]
    exact (Nat.div_add_mod' magnitudeBits (2 ^ 52)).symm
  have hexponentLe : exponentField ≤ 1022 := by
    have hdiv : exponentField * 2 ^ 52 ≤ magnitudeBits := by
      dsimp [exponentField]
      exact Nat.div_mul_le_self magnitudeBits (2 ^ 52)
    omega
  have hexponent :
      Wasm.IEEE64.exponent bits = exponentField := by
    change bits.toNat / 2 ^ 52 % 2 ^ 11 = exponentField
    rw [← Nat.mod_mul_right_div_self bits.toNat (2 ^ 52) (2 ^ 11)]
    rw [show 2 ^ 52 * 2 ^ 11 = 2 ^ 63 by norm_num,
      ← hmagnitudeBits]
  have hfraction :
      Wasm.IEEE64.fraction bits = fractionField := by
    change bits.toNat % 2 ^ 52 = fractionField
    calc
      bits.toNat % 2 ^ 52 =
          (bits.toNat % 2 ^ 63) % 2 ^ 52 :=
        (Nat.mod_mod_of_dvd bits.toNat
          (by norm_num : 2 ^ 52 ∣ 2 ^ 63)).symm
      _ = magnitudeBits % 2 ^ 52 := by rw [← hmagnitudeBits]
      _ = fractionField := rfl
  have hfinite : CodeLib.IEEE64.Finite bits := by
    simp [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexponent,
      show exponentField ≠ 0x7FF by omega]
  have hscaledMagnitude :
      Wasm.IEEE64.scaledMagnitude bits ≤ 2 ^ 1073 := by
    simp only [Wasm.IEEE64.scaledMagnitude, hexponent, hfraction]
    by_cases hzero : exponentField = 0
    · simp [hzero]
      change fractionField ≤ 2 ^ 1073
      have hpower : 2 ^ 52 ≤ 2 ^ 1073 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (Nat.le_of_lt hfractionLt).trans hpower
    · simp [hzero]
      by_cases htop : exponentField = 1022
      · have hfractionZero : fractionField = 0 := by
          omega
        rw [htop, hfractionZero]
      · have hexponentSmall : exponentField ≤ 1021 := by
          omega
        have hsignificand : 2 ^ 52 + fractionField ≤ 2 ^ 53 := by
          calc
            2 ^ 52 + fractionField ≤ 2 ^ 52 + 2 ^ 52 :=
              Nat.add_le_add_left (Nat.le_of_lt hfractionLt) _
            _ = 2 ^ 53 := by norm_num
        have hpower : 2 ^ (exponentField - 1) ≤ 2 ^ 1020 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        calc
          (2 ^ 52 + fractionField) * 2 ^ (exponentField - 1) ≤
              2 ^ 53 * 2 ^ 1020 := Nat.mul_le_mul hsignificand hpower
          _ = 2 ^ 1073 := by rw [← pow_add]
  refine ⟨hfinite, ?_⟩
  have hscaledAbs :
      |(Wasm.IEEE64.scaledValue bits : ℝ)| =
        Wasm.IEEE64.scaledMagnitude bits := by
    simp [Wasm.IEEE64.scaledValue]
    split <;> simp
  have hscaledMagnitudeReal :
      (Wasm.IEEE64.scaledMagnitude bits : ℝ) ≤ (2 : ℝ) ^ 1073 := by
    exact_mod_cast hscaledMagnitude
  have hdenominator : 0 < (2 : ℝ) ^ 1074 := by positivity
  rw [CodeLib.IEEE64.value, abs_div, abs_of_pos hdenominator, hscaledAbs]
  apply (div_le_iff₀ hdenominator).2
  calc
    (Wasm.IEEE64.scaledMagnitude bits : ℝ) ≤
        (2 : ℝ) ^ 1073 := hscaledMagnitudeReal
    _ = ((1 : ℝ) / 2) * (2 : ℝ) ^ 1074 := by
      rw [show 1074 = 1073 + 1 by omega, pow_succ]
      ring

#print axioms boundedByHalf_spec

end Project.F64Dot2CheckedBits.Bounds
