import LeanExe.ProofKit.F64PositiveOrder
import LeanExe.ProofKit.F64Sign
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64Bits

/-!
The tests that fdlibm's code makes on the high 32 bits of a binary64 word, as magnitudes.  `ix`,
the high word without its sign bit, is below `H` exactly when the magnitude is below the value of
the word with high word `H` and low word 0.  The sign test `hx >>> 31 == 1` is the sign bit, and
the comparisons `Wasm.IEEE64.lt` and `Wasm.IEEE64.eq` of finite words compare their values.
-/

namespace LeanExe.ProofKit.F64HighWord
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem abs_toNat (x : UInt64) : (Wasm.IEEE64.abs x).toNat = x.toNat % 2 ^ 63 := by
  have hx := x.toNat_lt
  simp only [Wasm.IEEE64.abs, Wasm.IEEE64.encodeFinite, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, UInt64.toNat_ofNat', Bool.false_eq_true, ite_false]
  omega

theorem value_abs (x : UInt64) : value (Wasm.IEEE64.abs x) = |value x| := by
  obtain ⟨he, hf, hs⟩ := F64Sign.fields_abs x
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.abs x) = Wasm.IEEE64.scaledMagnitude x := by
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf]
  have h1 : Wasm.IEEE64.scaledValue (Wasm.IEEE64.abs x) =
      (Wasm.IEEE64.scaledMagnitude x : Int) := by
    simp only [Wasm.IEEE64.scaledValue, hs, hm, Bool.false_eq_true, ite_false]
  have h2 : |(Wasm.IEEE64.scaledValue x : ℝ)| = (Wasm.IEEE64.scaledMagnitude x : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_scaledValue]
    norm_num
  simp only [value, h1, abs_div, h2, Int.cast_natCast]
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]

theorem high_toNat (x : UInt64) :
    ((x >>> 32) &&& 0x7fffffff).toNat = x.toNat % 2 ^ 63 / 2 ^ 32 := by
  have hx := x.toNat_lt
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight]
  rw [show (0x7fffffff : UInt64).toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
  omega

/-- The high word without the sign bit is below `H` exactly when the magnitude is below the value
of the word with high word `H` and low word 0. -/
theorem high_lt_iff (x : UInt64) (H : ℕ) (hH : H < 2 ^ 31) :
    ((x >>> 32) &&& 0x7fffffff).toNat < H ↔ |value x| < value (UInt64.ofNat (H * 2 ^ 32)) := by
  have hx := x.toNat_lt
  have hH' : H * 2 ^ 32 < 2 ^ 63 := by
    calc H * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hH (by positivity)
      _ = 2 ^ 63 := by norm_num
  have hw : (UInt64.ofNat (H * 2 ^ 32)).toNat = H * 2 ^ 32 :=
    UInt64.toNat_ofNat_of_lt' (hH'.trans (by norm_num))
  have ha : (Wasm.IEEE64.abs x).toNat < 2 ^ 63 := by rw [abs_toNat]; omega
  rw [high_toNat, ← value_abs, Nat.div_lt_iff_lt_mul (by positivity)]
  constructor
  · intro h
    apply F64PositiveOrder.value_strict (by rw [hw]; exact hH')
    rw [abs_toNat, hw]
    exact h
  · intro h
    by_contra hn
    have hle : (UInt64.ofNat (H * 2 ^ 32)).toNat ≤ (Wasm.IEEE64.abs x).toNat := by
      rw [abs_toNat, hw]
      omega
    have := (F64PositiveOrder.value_le_iff (by rw [hw]; exact hH') ha).mpr hle
    linarith

/-- `hx >>> 31 == 1` for the high word `hx` is the sign bit. -/
theorem sign_test (x : UInt64) : ((x >>> 32) >>> 31 == 1) = Wasm.IEEE64.sign x := by
  have hx := x.toNat_lt
  have hn : ((x >>> 32) >>> 31).toNat = x.toNat / 2 ^ 63 := by
    simp only [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      show (31 : UInt64).toNat % 64 = 31 from rfl, Nat.shiftRight_eq_div_pow]
    omega
  unfold Wasm.IEEE64.sign
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have h1 : (x >>> 32) >>> 31 = 1 := UInt64.toNat_inj.mp (by rw [hn]; simp; omega)
    rw [h1, beq_self_eq_true]
    exact (decide_eq_true h).symm
  · have h1 : (x >>> 32) >>> 31 ≠ 1 := fun he => by
      have := congrArg UInt64.toNat he
      rw [hn] at this
      simp at this
      omega
    rw [beq_eq_false_iff_ne.mpr h1]
    exact (decide_eq_false h).symm

/-- The high word of a finite word without its sign bit is below that of infinity. -/
theorem finite_high (x : UInt64) (hx : Finite x) :
    ((x >>> 32) &&& 0x7fffffff).toNat < 0x7ff00000 := by
  have h := hx
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
    ne_eq] at h
  rw [high_toNat]
  have := x.toNat_lt
  omega

theorem lt_iff_value (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.lt a b = true ↔ value a < value b := by
  simp only [Wasm.IEEE64.lt, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_false,
    Bool.false_eq_true, ite_false, decide_eq_true_eq, value]
  constructor
  · intro h
    exact div_lt_div_of_pos_right (by exact_mod_cast h) (by positivity)
  · intro h
    have := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp h
    exact_mod_cast this

theorem eq_iff_value (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.eq a b = true ↔ value a = value b := by
  simp only [Wasm.IEEE64.eq, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_false,
    Bool.false_eq_true, ite_false, beq_iff_eq, value]
  constructor
  · intro h
    rw [h]
  · intro h
    have := (div_left_inj' (by positivity : (2 : ℝ) ^ 1074 ≠ 0)).mp h
    exact_mod_cast this

theorem float_lt_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a < b ↔ value a.toBits < value b.toBits := by
  rw [F64Bits.lt_iff, lt_iff_value _ _ ha hb]

theorem float_beq_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    (a == b) = true ↔ value a.toBits = value b.toBits := by
  rw [F64Bits.beq_eq, eq_iff_value _ _ ha hb]

#print axioms abs_toNat
#print axioms value_abs
#print axioms high_lt_iff
#print axioms sign_test
#print axioms finite_high
#print axioms lt_iff_value
#print axioms eq_iff_value
#print axioms float_lt_iff
#print axioms float_beq_iff

end LeanExe.ProofKit.F64HighWord
