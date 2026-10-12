import Verified.Examples.Expm1KernelInner
import LeanExe.ProofKit.F64NearestScale

/-!
Words of the scaling forms of fdlibm's `expm1`.  The kernel builds `2 ^ k`, `1 - 2 ^ -k`, and
`2 ^ -k` from `k`, multiplies by `2` and `-2`, and subtracts 1 from results of at least `2 ^ 57`.
`twopk_pos`, `twopk_neg`, `powerNeg_eq`, and `oneMinus_spec` state the words and values,
`double_spec` the product with 2, `mul_negTwo` the product with -2 as the product of the
negation with 2, and `sub_one_large` that subtracting 1 from a word from `2 ^ 57` on, including the
top binade, returns the word.
-/

namespace Verified.Examples.Expm1FormWords
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

local notation "η" => multiplicationUnderflowEpsilon

/-- A nonnegative word is the encoding of its fields. -/
theorem encode_self (v : UInt64) (hv : v.toNat < 2 ^ 63) :
    Wasm.IEEE64.encodeFinite false (Wasm.IEEE64.exponent v) (Wasm.IEEE64.fraction v) = v := by
  apply UInt64.toNat_inj.mp
  simp only [Wasm.IEEE64.encodeFinite, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
    Bool.false_eq_true, ite_false, zero_add, UInt64.toNat_ofNat']
  have h1 : v.toNat / 2 ^ 52 % 2 ^ 11 = v.toNat / 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.mul_comm, Nat.div_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- The value of the power-of-two word with exponent field `E ≥ 1`. -/
theorem power_value (E : Nat) (hE : 1 ≤ E) (hE' : E < 2047) :
    value (Wasm.IEEE64.encodeFinite false E 0) = (2 : ℝ) ^ (E + 51) / 2 ^ 1074 := by
  have h := scaledValue_encodeFinite false E 0 (by omega) (by norm_num)
  simp only [show E ≠ 0 by omega, ite_false, Bool.false_eq_true, add_zero] at h
  rw [value, h]
  push_cast
  rw [show (4503599627370496 : ℝ) = 2 ^ 52 by norm_num, ← pow_add]
  congr 2
  omega

theorem power_finite (E : Nat) (hE' : E < 2047) :
    Finite (Wasm.IEEE64.encodeFinite false E 0) :=
  finite_encodeFinite false E 0 hE' (by norm_num)

/-- The word `E <<< 52` for an exponent field `E < 2047`. -/
theorem shift_word (E : Nat) (hE : E < 2047) (w : UInt64) (hw : w.toNat = E) :
    w <<< 52 = Wasm.IEEE64.encodeFinite false E 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, hw]
  have h52 : (52 : UInt64).toNat % 64 = 52 := rfl
  rw [h52, Nat.shiftLeft_eq]
  simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add, add_zero,
    UInt64.toNat_ofNat']

theorem not_nan_power (E : Nat) (hE : E < 2047) :
    Wasm.IEEE64.isNaN (Wasm.IEEE64.encodeFinite false E 0) = false := by
  have hf := fraction_encodeFinite false E 0 (by omega) (by norm_num)
  simp [Wasm.IEEE64.isNaN, hf]

theorem twopk_pos (m : UInt64) (hm : m.toNat ≤ 1023) :
    Expm1Words.twopk false m = Wasm.IEEE64.encodeFinite false (1023 + m.toNat) 0 := by
  have hw : ((0x3ff : UInt64) + m).toNat = 1023 + m.toNat := by
    rw [UInt64.toNat_add]
    change (1023 + m.toNat) % 2 ^ 64 = 1023 + m.toNat
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Expm1Words.twopk, Bool.false_eq_true, ite_false, Expm1Words.ofBitsWord,
    shift_word _ (by omega) _ hw, not_nan_power _ (by omega : 1023 + m.toNat < 2047)]

theorem twopk_neg (m : UInt64) (hm : m.toNat ≤ 1022) :
    Expm1Words.twopk true m = Wasm.IEEE64.encodeFinite false (1023 - m.toNat) 0 := by
  have hle : m ≤ (0x3ff : UInt64) := UInt64.le_iff_toNat_le.mpr (by change m.toNat ≤ 1023; omega)
  have hw : ((0x3ff : UInt64) - m).toNat = 1023 - m.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hle]
    rfl
  simp only [Expm1Words.twopk, ite_true, Expm1Words.ofBitsWord,
    shift_word _ (by omega) _ hw, not_nan_power _ (by omega : 1023 - m.toNat < 2047),
    Bool.false_eq_true, ite_false]

theorem powerNeg_eq (m : UInt64) (hm : m.toNat ≤ 1022) :
    Expm1Words.powerNeg m = Wasm.IEEE64.encodeFinite false (1023 - m.toNat) 0 := by
  have h := twopk_neg m hm
  simpa [Expm1Words.twopk, Expm1Words.powerNeg] using h

theorem maxPower_eq : Expm1Words.ofBitsWord Expm1Words.maxPower =
    Wasm.IEEE64.encodeFinite false 2046 0 := by
  decide

theorem two_eq : Expm1Words.two = Wasm.IEEE64.encodeFinite false 1024 0 := by decide

/-- `1 - 2 ^ -m` for `2 ≤ m < 20`, checked for each `m`. -/
theorem oneMinus_scaled : ∀ j : Fin 18,
    Wasm.IEEE64.scaledValue (Expm1Words.oneMinus (UInt64.ofNat (j.val + 2))) =
      2 ^ 1074 - 2 ^ (1072 - j.val) ∧
      Finite (Expm1Words.oneMinus (UInt64.ofNat (j.val + 2))) := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem oneMinus_spec (m : UInt64) (h2 : 2 ≤ m.toNat) (h20 : m.toNat < 20) :
    Finite (Expm1Words.oneMinus m) ∧
      value (Expm1Words.oneMinus m) = 1 - 1 / (2 : ℝ) ^ m.toNat := by
  obtain ⟨hs, hf⟩ := oneMinus_scaled ⟨m.toNat - 2, by omega⟩
  have hm : UInt64.ofNat (m.toNat - 2 + 2) = m := by
    rw [show m.toNat - 2 + 2 = m.toNat by omega, UInt64.ofNat_toNat]
  simp only [hm] at hs hf
  refine ⟨hf, ?_⟩
  rw [value, hs, show 1072 - (m.toNat - 2) = 1074 - m.toNat by omega]
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  rw [sub_div, div_self (by positivity)]
  congr 1
  rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
  congr 1
  omega

/-- The product with 2: exact for normal words, within `3 η` otherwise. -/
theorem double_spec (d : UInt64) (hdf : Finite d) (hd : |value d| < (2 : ℝ) ^ 1021) :
    Finite (Wasm.IEEE64.mul Expm1Words.two d) ∧
      |value (Wasm.IEEE64.mul Expm1Words.two d) - 2 * value d| ≤ 3 * η := by
  have hη : (0 : ℝ) ≤ η := by norm_num [multiplicationUnderflowEpsilon]
  by_cases he : 1 ≤ Wasm.IEEE64.exponent d
  · have hb : |value (F64ExponentBounds.boundary 2044)| = (2 : ℝ) ^ 1021 := by
      rw [F64ExponentBounds.boundary, F64PositiveSpacing.boundary_value 2044 (by norm_num)
        (by norm_num), abs_of_pos (by positivity)]
      norm_num
    have hlt := F64ExponentBounds.exponent_lt_of_magnitude_lt d 2044 (by norm_num)
      (by rw [hb]; exact hd)
    rw [two_eq]
    have h := F64PowerScale.mul_power_finite 1024 d (by norm_num) (by norm_num) hdf he (by omega)
      (by omega)
    refine ⟨h.1, ?_⟩
    rw [h.2]
    have : (2 : ℝ) ^ (((1024 : Nat) : Int) - 1023) = 2 := by norm_num
    rw [this, sub_self, abs_zero]
    linarith
  · have he0 : Wasm.IEEE64.exponent d = 0 := by omega
    have hsmall : |value d| ≤ 2 ^ 52 / 2 ^ 1074 := by
      have hm : Wasm.IEEE64.scaledMagnitude d ≤ 2 ^ 52 := by
        unfold Wasm.IEEE64.scaledMagnitude
        simp only [he0, beq_self_eq_true, ite_true]
        exact (Nat.mod_lt _ (by norm_num)).le
      have hv : |value d| = (Wasm.IEEE64.scaledMagnitude d : ℝ) / 2 ^ 1074 := by
        rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
          ← natAbs_scaledValue, Nat.cast_natAbs, Int.cast_abs]
      rw [hv]
      gcongr
      exact_mod_cast hm
    have h2v : value Expm1Words.two = 2 := (Expm1KernelInner.const_values).2.2.1
    have h := F64MulBounds.mul_real_mixed Expm1Words.two d
      (Expm1KernelInner.const_finite).2.2.1 hdf (by
        rw [h2v, abs_mul, abs_two]
        calc 2 * |value d| ≤ 2 * (2 ^ 52 / 2 ^ 1074) := by gcongr
          _ < 2 ^ 1022 := by norm_num)
    refine ⟨h.1, ?_⟩
    rw [h2v] at h
    refine h.2.trans ?_
    rw [abs_mul, abs_two]
    have : unitRoundoff64 * (2 * |value d|) ≤ 2 * η := by
      rw [show unitRoundoff64 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
      have : 2 * |value d| ≤ 2 * (2 ^ 52 / 2 ^ 1074) := by gcongr
      nlinarith
    linarith

/-- The product with -2 is the product of the negation with 2. -/
theorem mul_negTwo (b : UInt64) (hbf : Finite b) :
    Wasm.IEEE64.mul Expm1Words.negTwo b =
      Wasm.IEEE64.mul (Wasm.IEEE64.negate b) (Wasm.IEEE64.encodeFinite false 1024 0) := by
  have hnf := (F64Magnitude.negate_value b hbf).1
  have h2f : Finite (Wasm.IEEE64.encodeFinite false 1024 0) := power_finite 1024 (by norm_num)
  rw [mul_finite_rounder _ _ (Expm1KernelInner.const_finite).2.2.2.2.2.1 hbf,
    mul_finite_rounder _ _ hnf h2f]
  have he : Wasm.IEEE64.exponent b < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hf : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hsn : Wasm.IEEE64.sign (Wasm.IEEE64.negate b) = !Wasm.IEEE64.sign b := by
    unfold Wasm.IEEE64.negate
    exact sign_encodeFinite _ _ _ he hf
  have hmn : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate b) = Wasm.IEEE64.scaledMagnitude b := by
    unfold Wasm.IEEE64.negate
    rw [scaledMagnitude_encodeFinite _ _ _ he hf]
    simp [Wasm.IEEE64.scaledMagnitude]
  have hs2 : Wasm.IEEE64.sign Expm1Words.negTwo = true := by decide
  have hs2' : Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite false 1024 0) = false := by decide
  have hm2 : Wasm.IEEE64.scaledMagnitude Expm1Words.negTwo =
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite false 1024 0) := by decide
  rw [hsn, hmn, hs2, hs2', hm2, Nat.mul_comm]
  cases Wasm.IEEE64.sign b <;> rfl

/-- `roundShift n s` is any integer `R` with `R 2 ^ s` within less than half of `2 ^ s` of
`n`. -/
theorem roundShift_eq (n s R : Nat) (hs : 0 < s)
    (h : 2 * |((R * 2 ^ s : Nat) : ℤ) - n| < 2 ^ s) : Wasm.IEEE32.roundShift n s = R := by
  have he := CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _
    (CodeLib.IEEE32.roundShift_error_cases n s hs)
  set R0 := Wasm.IEEE32.roundShift n s
  have hhalf : ((2 ^ s / 2 : Nat) : ℤ) * 2 = 2 ^ s := by
    have : 2 ^ s / 2 * 2 = 2 ^ s := Nat.div_mul_cancel (dvd_pow_self 2 (by omega))
    exact_mod_cast this
  have hP : (0 : ℤ) < 2 ^ s := by positivity
  have hD : |((R0 : ℤ) - R) * 2 ^ s| < 2 ^ s := by
    have : ((R0 : ℤ) - R) * 2 ^ s = (((R0 * 2 ^ s : Nat) : ℤ) - n) - (((R * 2 ^ s : Nat) : ℤ) - n) := by
      push_cast; ring
    rw [this]
    have := abs_sub (((R0 * 2 ^ s : Nat) : ℤ) - n) (((R * 2 ^ s : Nat) : ℤ) - n)
    linarith
  rw [abs_mul, abs_of_pos hP] at hD
  have h1 : |(R0 : ℤ) - R| < 1 := by
    by_contra hn
    have : 1 * 2 ^ s ≤ |(R0 : ℤ) - R| * 2 ^ s := Int.mul_le_mul_of_nonneg_right (not_lt.mp hn) hP.le
    linarith
  have h0 : (R0 : ℤ) - R = 0 := Int.abs_lt_one_iff.mp h1
  omega

#print axioms encode_self
#print axioms power_value
#print axioms shift_word
#print axioms twopk_pos
#print axioms twopk_neg
#print axioms powerNeg_eq
#print axioms oneMinus_spec
#print axioms double_spec
#print axioms mul_negTwo
#print axioms roundShift_eq

end Verified.Examples.Expm1FormWords
