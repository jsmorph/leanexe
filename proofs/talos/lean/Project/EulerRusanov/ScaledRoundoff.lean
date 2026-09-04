import Project.EulerRusanov.Model

/-!
# Scale-aware binary64 roundoff lemmas for Euler--Rusanov

The generic `CodeLib.IEEE64` absolute-error theorems use unit bounds on each
operand.  Several intermediates in the Euler flux are deliberately larger
than one, even though the exact result of the operation remains small.  This
module derives the two thin variants needed by the case proof directly from
CodeLib's scaled-integer packing specifications:

* addition is finite with absolute error at most `2^-52` when the exact sum
  has magnitude strictly below four;
* multiplication is finite with the same conservative absolute-error bound
  when the exact product has magnitude strictly below two.

It also connects the generated integer `xor` sign toggle to exact negation of
the represented finite real value.  No native `Float` evaluation is used.
-/

namespace Project.EulerRusanov.ScaledRoundoff

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

open Wasm
open CodeLib.IEEE64

/-! ## Scale-aware addition -/

/-- A finite binary64 addition whose exact real sum has magnitude below four
remains finite and incurs at most one conservative binary64 arithmetic unit
of absolute error.  Unlike `CodeLib.IEEE64.add_real_error`, this theorem does
not require separate unit bounds on the operands, so cancellation is allowed.
-/
theorem add_real_error_of_exact_sum_lt_four
    (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hsum : |value a + value b| < (4 : ℝ)) :
    Finite (IEEE64.add a b) ∧
      |value (IEEE64.add a b) - (value a + value b)| ≤
        arithmeticEpsilon := by
  let z : Int := IEEE64.scaledValue a + IEEE64.scaledValue b
  have hzReal : |(z : ℝ)| < (2 : ℝ) ^ 1076 := by
    have hzValue :
        (z : ℝ) = (value a + value b) * (2 : ℝ) ^ 1074 := by
      simp only [z, value, Int.cast_add]
      field_simp
    rw [hzValue, abs_mul,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 1074)]
    calc
      |value a + value b| * (2 : ℝ) ^ 1074 <
          4 * (2 : ℝ) ^ 1074 :=
        mul_lt_mul_of_pos_right hsum (by positivity)
      _ = (2 : ℝ) ^ 1076 := by norm_num
  have hzInt : |z| < (2 ^ 1076 : Int) := by
    exact_mod_cast hzReal
  have hzBound : z.natAbs < 2 ^ 1076 := natAbs_lt_nat hzInt
  have hs := add_spec a b ha hb (by simpa [z] using hzBound)
  constructor
  · exact hs.1
  · let error : Int :=
      IEEE64.scaledValue (IEEE64.add a b) -
        (IEEE64.scaledValue a + IEEE64.scaledValue b)
    have herror : |error| ≤ (2 ^ 1022 : Nat) := by
      simpa [error] using hs.2
    have herrorEq :
        value (IEEE64.add a b) - (value a + value b) =
          (error : ℝ) / (2 : ℝ) ^ 1074 := by
      simp [value, error]
      ring
    rw [herrorEq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 1074)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 1074)).2
    have herrorReal : |(error : ℝ)| ≤ (2 : ℝ) ^ 1022 := by
      exact_mod_cast herror
    calc
      |(error : ℝ)| ≤ (2 : ℝ) ^ 1022 := herrorReal
      _ = arithmeticEpsilon * (2 : ℝ) ^ 1074 := by
        norm_num [arithmeticEpsilon]

/-! ## Scale-aware multiplication -/

/-- A finite binary64 multiplication whose exact real product has magnitude
below two remains finite and incurs at most `2^-52` absolute error.  The proof
uses the exact-product hypothesis to establish the scaled dyadic packer's
range directly; neither operand is required to be bounded by one.
-/
theorem mul_real_error_of_exact_product_lt_two
    (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hproduct : |value a * value b| < (2 : ℝ)) :
    Finite (IEEE64.mul a b) ∧
      |value (IEEE64.mul a b) - value a * value b| ≤
        multiplicationEpsilon := by
  let n := IEEE64.scaledMagnitude a * IEEE64.scaledMagnitude b
  have hscaledAbs (x : UInt64) :
      |(IEEE64.scaledValue x : ℝ)| =
        (IEEE64.scaledMagnitude x : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_scaledValue]
    norm_num
  have hproductAbs :
      |value a * value b| = (n : ℝ) / (2 : ℝ) ^ 2148 := by
    simp [value, n, abs_mul, abs_div, hscaledAbs]
    ring
  rw [hproductAbs] at hproduct
  have hnReal : (n : ℝ) < (2 : ℝ) ^ 2149 := by
    calc
      (n : ℝ) < 2 * (2 : ℝ) ^ 2148 :=
        (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ 2148)).mp hproduct
      _ = (2 : ℝ) ^ 2149 := by norm_num
  have hnReal' : (n : ℝ) < ((2 ^ 2149 : Nat) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnReal
  have hn : n < 2 ^ 2149 := by
    exact_mod_cast hnReal'
  have hs := roundDyadicMagnitude1074_spec
    (IEEE64.sign a != IEEE64.sign b) n hn
  have hmul := mul_finite_rounder a b ha hb
  rw [hmul]
  constructor
  · exact hs.1
  · let error : Int :=
      IEEE64.scaledValue
          (IEEE64.roundDyadicMagnitude
            (IEEE64.sign a != IEEE64.sign b) n 1074) *
          (2 : Int) ^ 1074 -
        IEEE64.scaledValue a * IEEE64.scaledValue b
    have herror : |error| ≤ (2 ^ 2096 : Nat) := by
      have hround := hs.2.2
      have hresultSign := hs.2.1
      have habs (x y : Int) : |-x + y| = |x + -y| := by
        rw [show -x + y = -(x + -y) by ring, abs_neg]
      cases hsa : IEEE64.sign a <;>
        cases hsb : IEEE64.sign b <;>
        simp [n, hsa, hsb] at hresultSign <;>
        simp [IEEE64.scaledValue, hresultSign, hsa, hsb, n, error]
          at hround ⊢
      all_goals
        first
        | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using hround
        | rw [habs]
          simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using hround
    have herrorEq :
        value (IEEE64.roundDyadicMagnitude
            (IEEE64.sign a != IEEE64.sign b) n 1074) -
            value a * value b =
          (error : ℝ) / (2 : ℝ) ^ 2148 := by
      simp [value, error]
      field_simp
      ring
    rw [herrorEq, abs_div,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 2148)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 2148)).2
    have herrorReal : |(error : ℝ)| ≤ (2 : ℝ) ^ 2096 := by
      exact_mod_cast herror
    calc
      |(error : ℝ)| ≤ (2 : ℝ) ^ 2096 := herrorReal
      _ = multiplicationEpsilon * (2 : ℝ) ^ 2148 := by
        norm_num [multiplicationEpsilon]

/-! ## Integer sign toggle -/

private theorem signMask_toNat :
    Model.signMask.toNat = 2 ^ 63 := by
  rw [Model.signMask]
  exact UInt64.toNat_ofNat_of_lt (by norm_num [UInt64.size])

private theorem sign_eq_msb (x : UInt64) :
    IEEE64.sign x = x.toBitVec.msb := by
  symm
  simpa [IEEE64.sign] using (BitVec.msb_eq_decide x.toBitVec)

/-- Toggling bit 63 leaves the binary64 exponent field unchanged. -/
theorem exponent_negateBits (x : UInt64) :
    IEEE64.exponent (Model.negateBits x) = IEEE64.exponent x := by
  simp only [Model.negateBits, IEEE64.exponent,
    UInt64.toNat_xor]
  rw [signMask_toNat]
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
  norm_num

/-- Toggling bit 63 leaves the binary64 fraction field unchanged. -/
theorem fraction_negateBits (x : UInt64) :
    IEEE64.fraction (Model.negateBits x) = IEEE64.fraction x := by
  simp only [Model.negateBits, IEEE64.fraction,
    UInt64.toNat_xor]
  rw [signMask_toNat]
  rw [Nat.xor_mod_two_pow]
  norm_num

/-- Toggling bit 63 complements exactly the binary64 sign field. -/
theorem sign_negateBits (x : UInt64) :
    IEEE64.sign (Model.negateBits x) = !IEEE64.sign x := by
  have hmask : Model.signMask.toBitVec.msb = true := by
    rw [← sign_eq_msb]
    simp [IEEE64.sign, signMask_toNat]
  rw [sign_eq_msb (Model.negateBits x), sign_eq_msb x]
  simp [Model.negateBits, hmask]

/-- Toggling the sign bit preserves the unsigned scaled magnitude. -/
theorem scaledMagnitude_negateBits (x : UInt64) :
    IEEE64.scaledMagnitude (Model.negateBits x) =
      IEEE64.scaledMagnitude x := by
  simp only [IEEE64.scaledMagnitude, exponent_negateBits,
    fraction_negateBits]

/-- Toggling the sign bit preserves finiteness. -/
theorem negateBits_finite (x : UInt64) (h : CodeLib.IEEE64.Finite x) :
    CodeLib.IEEE64.Finite (Model.negateBits x) := by
  change IEEE64.isFinite (Model.negateBits x) = true
  change IEEE64.isFinite x = true at h
  simpa only [IEEE64.isFinite, exponent_negateBits] using h

/-- At the common `2^-1074` integer scale, xor with the sign mask is exact
additive negation.  This statement also distinguishes the two signed-zero
encodings through the separate `sign_negateBits` theorem above.
-/
theorem scaledValue_negateBits (x : UInt64) :
    IEEE64.scaledValue (Model.negateBits x) =
      -IEEE64.scaledValue x := by
  rw [IEEE64.scaledValue, IEEE64.scaledValue,
    scaledMagnitude_negateBits, sign_negateBits]
  cases hsign : IEEE64.sign x <;> simp

/-- Xor with the sign mask is exact negation of the modeled real value. -/
theorem value_negateBits (x : UInt64) :
    value (Model.negateBits x) = -value x := by
  rw [value, value, scaledValue_negateBits]
  simp only [Int.cast_neg]
  ring

/-- Combined finite/value specification used at each generated jump. -/
theorem negateBits_real_spec (x : UInt64) (h : Finite x) :
    Finite (Model.negateBits x) ∧
      value (Model.negateBits x) = -value x :=
  ⟨negateBits_finite x h, value_negateBits x⟩

#print axioms add_real_error_of_exact_sum_lt_four
#print axioms mul_real_error_of_exact_product_lt_two
#print axioms negateBits_real_spec

end Project.EulerRusanov.ScaledRoundoff
