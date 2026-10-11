import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64Sterbenz

/-!
The high word of a binary64 value: `w &&& 0xFFFFFFFF00000000` clears the low 32 bits of the
fraction.  The result keeps the sign and the exponent field, so it is finite when `w` is, and its
scaled magnitude is `ma 2 ^ (32 + e - 1)` with `ma < 2 ^ 21` for exponent field `e`, so it
multiplies a constant of 32 significant bits exactly.  It differs from `w` by at most
`|w| / 2 ^ 20`, or by less than `2 ^ -1040` for a subnormal `w`.
-/

namespace LeanExe.ProofKit.F64HighWord
open CodeLib.IEEE64

/-- The word with the low 32 bits cleared. -/
def high (w : UInt64) : UInt64 := w &&& 0xFFFFFFFF00000000

theorem high_toNat (w : UInt64) : (high w).toNat = w.toNat / 4294967296 * 4294967296 := by
  have hw := w.toNat_lt
  unfold high
  rw [UInt64.toNat_and]
  simp only [UInt64.reduceToNat]
  apply Nat.eq_of_testBit_eq
  intro j
  have hm : (18446744069414584320 : Nat) = (2 ^ 32 - 1) * 2 ^ 32 := by norm_num
  have hp : (4294967296 : Nat) = 2 ^ 32 := by norm_num
  rw [hm, hp, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : 32 ≤ j
  · have he : j - 32 + 32 = j := by omega
    rw [he]
    by_cases hj2 : j < 64
    · simp [hj, show j - 32 < 32 by omega]
    · have h1 : w.toNat.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1]
  · simp [hj]

theorem high_fields (w : UInt64) :
    Wasm.IEEE64.exponent (high w) = Wasm.IEEE64.exponent w ∧
      Wasm.IEEE64.sign (high w) = Wasm.IEEE64.sign w ∧
      Wasm.IEEE64.fraction (high w) = Wasm.IEEE64.fraction w / 4294967296 * 4294967296 := by
  have h := high_toNat w
  have hw := w.toNat_lt
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.sign, Wasm.IEEE64.fraction, h, Nat.reducePow]
  simp only [Nat.reducePow] at hw
  refine ⟨by omega, ?_, by omega⟩
  congr 1
  apply propext
  omega

theorem high_finite (w : UInt64) (hw : Finite w) : Finite (high w) := by
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, (high_fields w).1]
  exact hw

theorem high_magnitude (w : UInt64) :
    ∃ ma : Nat, Wasm.IEEE64.scaledMagnitude (high w) =
      ma * 2 ^ (32 + (Wasm.IEEE64.exponent w - 1)) ∧ ma < 2 ^ 21 := by
  obtain ⟨he, -, hf⟩ := high_fields w
  have hflt : Wasm.IEEE64.fraction w < 4503599627370496 := Nat.mod_lt _ (by norm_num)
  unfold Wasm.IEEE64.scaledMagnitude
  rw [he, hf]
  by_cases h0 : Wasm.IEEE64.exponent w = 0
  · refine ⟨Wasm.IEEE64.fraction w / 4294967296, ?_, by simp only [Nat.reducePow]; omega⟩
    simp only [h0, beq_self_eq_true, ↓reduceIte, Nat.zero_sub, add_zero]
    norm_num
  · refine ⟨2 ^ 20 + Wasm.IEEE64.fraction w / 4294967296, ?_, by simp only [Nat.reducePow]; omega⟩
    have h' : (Wasm.IEEE64.exponent w == 0) = false := by simpa using h0
    simp only [h', Bool.false_eq_true, ↓reduceIte, pow_add]
    ring

theorem high_le (w : UInt64) :
    Wasm.IEEE64.scaledMagnitude (high w) ≤ Wasm.IEEE64.scaledMagnitude w ∧
      (Wasm.IEEE64.scaledMagnitude w - Wasm.IEEE64.scaledMagnitude (high w)) * 2 ^ 20 ≤
        Wasm.IEEE64.scaledMagnitude w + 2 ^ 54 := by
  obtain ⟨he, -, hf⟩ := high_fields w
  have hflt : Wasm.IEEE64.fraction w < 4503599627370496 := Nat.mod_lt _ (by norm_num)
  unfold Wasm.IEEE64.scaledMagnitude
  rw [he, hf]
  by_cases h0 : Wasm.IEEE64.exponent w = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte, Nat.reducePow]
    omega
  · have h' : (Wasm.IEEE64.exponent w == 0) = false := by simpa using h0
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    set q := 2 ^ (Wasm.IEEE64.exponent w - 1) with hq
    have h1 : 2 ^ 52 + Wasm.IEEE64.fraction w / 4294967296 * 4294967296 ≤
        2 ^ 52 + Wasm.IEEE64.fraction w := by omega
    have h2 : (2 ^ 52 + Wasm.IEEE64.fraction w - (2 ^ 52 + Wasm.IEEE64.fraction w / 4294967296 *
        4294967296)) * 2 ^ 20 ≤ 2 ^ 52 + Wasm.IEEE64.fraction w := by
      simp only [Nat.reducePow]
      omega
    refine ⟨Nat.mul_le_mul_right _ h1, ?_⟩
    rw [← Nat.sub_mul]
    calc (2 ^ 52 + Wasm.IEEE64.fraction w - (2 ^ 52 + Wasm.IEEE64.fraction w / 4294967296 *
          4294967296)) * q * 2 ^ 20
        = (2 ^ 52 + Wasm.IEEE64.fraction w - (2 ^ 52 + Wasm.IEEE64.fraction w / 4294967296 *
          4294967296)) * 2 ^ 20 * q := by ring
      _ ≤ (2 ^ 52 + Wasm.IEEE64.fraction w) * q := Nat.mul_le_mul_right _ h2
      _ ≤ (2 ^ 52 + Wasm.IEEE64.fraction w) * q + 2 ^ 54 := Nat.le_add_right _ _

/-- The high word differs from `w` by at most `|w| / 2 ^ 20 + 2 ^ -1040`. -/
theorem high_close (w : UInt64) :
    |value w - value (high w)| ≤ |value w| / 2 ^ 20 + 1 / 2 ^ 1040 := by
  obtain ⟨-, hs, -⟩ := high_fields w
  obtain ⟨hle, hkey⟩ := high_le w
  have hdiff : |value w - value (high w)| * 2 ^ 1074 =
      (Wasm.IEEE64.scaledMagnitude w : ℝ) - Wasm.IEEE64.scaledMagnitude (high w) := by
    have hle' : (Wasm.IEEE64.scaledMagnitude (high w) : ℝ) ≤ Wasm.IEEE64.scaledMagnitude w := by
      exact_mod_cast hle
    have hv : value w - value (high w) = (if Wasm.IEEE64.sign w then -1 else 1) *
        (((Wasm.IEEE64.scaledMagnitude w : ℝ) - Wasm.IEEE64.scaledMagnitude (high w)) / 2 ^ 1074) := by
      simp only [value, Wasm.IEEE64.scaledValue, hs]
      split <;> push_cast <;> ring
    rw [hv, abs_mul]
    have h1 : |(if Wasm.IEEE64.sign w then -1 else 1 : ℝ)| = 1 := by split <;> norm_num
    rw [h1, one_mul, abs_div, abs_of_nonneg (by linarith), abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      div_mul_cancel₀ _ (by positivity)]
  have habs := F64Sterbenz.value_abs_scaled w
  have hkeyR : ((Wasm.IEEE64.scaledMagnitude w : ℝ) - Wasm.IEEE64.scaledMagnitude (high w)) * 2 ^ 20 ≤
      (Wasm.IEEE64.scaledMagnitude w : ℝ) + 2 ^ 54 := by
    have h := hkey
    have h' : (((Wasm.IEEE64.scaledMagnitude w - Wasm.IEEE64.scaledMagnitude (high w)) * 2 ^ 20 : Nat) :
        ℝ) ≤ ((Wasm.IEEE64.scaledMagnitude w + 2 ^ 54 : Nat) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hle] at h'
    norm_num at h' ⊢ <;> linarith
  rw [← hdiff, ← habs] at hkeyR
  have h1074 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have h20 : (0 : ℝ) < 2 ^ 20 := by positivity
  have hfin : |value w - value (high w)| * (2 ^ 1074 * 2 ^ 20) ≤
      (|value w| / 2 ^ 20 + 1 / 2 ^ 1040) * (2 ^ 1074 * 2 ^ 20) := by
    have e1 : (|value w| / 2 ^ 20 + 1 / 2 ^ 1040) * (2 ^ 1074 * 2 ^ 20) =
        |value w| * 2 ^ 1074 + 2 ^ 54 := by
      field_simp <;> ring
    rw [e1]
    linarith
  exact le_of_mul_le_mul_right hfin (by positivity)

#print axioms high_toNat
#print axioms high_fields
#print axioms high_finite
#print axioms high_magnitude
#print axioms high_le
#print axioms high_close

end LeanExe.ProofKit.F64HighWord
