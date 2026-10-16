import LeanExe.ProofKit.F64PositiveRounding
import LeanExe.ProofKit.F64NearestBinade
import LeanExe.ProofKit.F64ExponentBounds

/-!
Relations between the fields of a binary64 word and its value: the exponent field bounds the
magnitude and the magnitude bounds the exponent field, the sign bit is the sign of a nonzero value,
and a positive normal word has the value of its fields.
-/

namespace LeanExe.ProofKit.F64Magnitude
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder

set_option exponentiation.threshold 4096

theorem value_zero : value (0 : UInt64) = 0 := by
  have h : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide +kernel
  rw [value, h, Int.cast_zero, zero_div]

/-- The binade boundary of exponent field 0, as `F64ExponentBounds.boundary 0` unfolds. -/
theorem value_zero_boundary : value (UInt64.ofNat (0 * 2 ^ 52)) = 0 := by
  rw [show UInt64.ofNat (0 * 2 ^ 52) = 0 from rfl]
  exact value_zero

theorem negate_value (y : UInt64) (hy : Finite y) :
    Finite (Wasm.IEEE64.negate y) ∧ value (Wasm.IEEE64.negate y) = -value y := by
  have h := negate_spec y hy
  refine ⟨h.1, ?_⟩
  simp only [value, h.2]
  push_cast
  ring

/-- The sign bit of a word with nonzero magnitude is the sign of its value. -/
theorem sign_value (x : UInt64) (hx : 0 < Wasm.IEEE64.scaledMagnitude x) :
    (Wasm.IEEE64.sign x = true ↔ value x < 0) := by
  have h2 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hm : (0 : ℝ) < (Wasm.IEEE64.scaledMagnitude x : ℝ) := by exact_mod_cast hx
  cases hs : Wasm.IEEE64.sign x
  · simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Int.cast_natCast, false_iff, not_lt]
    positivity
  · simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast,
      true_iff, neg_div]
    have := div_pos hm h2
    linarith

theorem normal_value (w : UInt64) (hs : Wasm.IEEE64.sign w = false)
    (he : 0 < Wasm.IEEE64.exponent w) :
    value w = ((2 : ℝ) ^ 52 + (Wasm.IEEE64.fraction w : ℝ)) *
      (2 : ℝ) ^ (Wasm.IEEE64.exponent w - 1) / (2 : ℝ) ^ 1074 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hs, Nat.ne_of_gt he]

theorem positive_encoding_toNat (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    (Wasm.IEEE64.encodeFinite false e f).toNat = e * 2 ^ 52 + f := by
  simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add,
    UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- A finite word with a clear sign bit lies below the encoding of positive infinity. -/
theorem lt_limit_of_finite (c : UInt64) (hcf : Finite c) (hcs : Wasm.IEEE64.sign c = false) :
    c.toNat < limit := by
  have hl : limit = 0x7FF0000000000000 := rfl
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
    ne_eq] at hcf
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hcs
  rw [hl]
  omega

/-- A nonnegative finite word has value below `2 ^ 1024`. -/
theorem finite_below_overflow (c : UInt64) (h : c.toNat < limit) :
    value c < (2 : ℝ) ^ 1024 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hle := (value_le_iff (h.trans hlim)
    (by decide : (0x7FEFFFFFFFFFFFFF : UInt64).toNat < 2 ^ 63)).mpr (by
      change c.toNat < 0x7FF0000000000000 at h
      change c.toNat ≤ 0x7FEFFFFFFFFFFFFF
      omega)
  rw [F64PositiveRounding.largest_finite_value] at hle
  have h971 : (0 : ℝ) < 2 ^ 971 := by positivity
  linarith

theorem magnitude_lt_of_exponent_lt (y : UInt64) (e : Nat) (he : 1 ≤ e)
    (h : Wasm.IEEE64.exponent y < e) :
    Wasm.IEEE64.scaledMagnitude y < 2 ^ (51 + e) := by
  have hf : Wasm.IEEE64.fraction y < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq]
  split_ifs with h0
  · exact lt_of_lt_of_le hf (Nat.pow_le_pow_right (by norm_num) (by omega))
  · calc
      (2 ^ 52 + Wasm.IEEE64.fraction y) * 2 ^ (Wasm.IEEE64.exponent y - 1) <
          2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent y - 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2 ^ (53 + (Wasm.IEEE64.exponent y - 1)) := by rw [pow_add]
      _ ≤ 2 ^ (51 + e) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A word whose exponent field is below `e` has magnitude below `2 ^ (e - 1023)`. -/
theorem magnitude_lt (x : UInt64) (e : Nat) (q : Int) (he1 : 1 ≤ e) (hq : (e : Int) = q + 1023)
    (he : Wasm.IEEE64.exponent x < e) : |value x| < (2 : ℝ) ^ q := by
  have hm := magnitude_lt_of_exponent_lt x e he1 he
  rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  have h1 : |(Wasm.IEEE64.scaledValue x : ℝ)| = (Wasm.IEEE64.scaledMagnitude x : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, natAbs_scaledValue, Int.cast_natCast]
  rw [h1, div_lt_iff₀ (by positivity)]
  have hm' : (Wasm.IEEE64.scaledMagnitude x : ℝ) < (2 : ℝ) ^ (51 + e) := by exact_mod_cast hm
  calc
    _ < (2 : ℝ) ^ (51 + e) := hm'
    _ = (2 : ℝ) ^ q * (2 : ℝ) ^ 1074 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      push_cast
      omega

/-- A word whose exponent field is at least `e` has magnitude at least `2 ^ (e - 1023)`. -/
theorem magnitude_ge (x : UInt64) (e : Nat) (q : Int) (he1 : 1 ≤ e) (he2 : e < 2048)
    (hq : (e : Int) = q + 1023) (he : e ≤ Wasm.IEEE64.exponent x) : (2 : ℝ) ^ q ≤ |value x| := by
  by_contra h
  have hb : value (F64ExponentBounds.boundary e) = (2 : ℝ) ^ q :=
    F64NearestBinade.boundary_power e q he1 he2 hq
  have hlt : |value x| < |value (F64ExponentBounds.boundary e)| := by
    rw [hb, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) q)]
    exact lt_of_not_ge h
  have := F64ExponentBounds.exponent_lt_of_magnitude_lt x e he2 hlt
  omega

/-- A word with value at least `2 ^ (e - 1023)` has exponent field at least `e`. -/
theorem exponent_ge_of_value (y : UInt64) (e : Nat) (he : 1 ≤ e)
    (hy : (2 : ℝ) ^ ((e : Int) - 1023) ≤ value y) : e ≤ Wasm.IEEE64.exponent y := by
  by_contra h
  have hm := magnitude_lt y e ((e : Int) - 1023) he (by ring) (by omega)
  have := le_abs_self (value y)
  linarith

/-- A word with value at least 1 has exponent field at least 1023. -/
theorem exponent_ge_of_one_le (y : UInt64) (hy : 1 ≤ value y) : 1023 ≤ Wasm.IEEE64.exponent y :=
  exponent_ge_of_value y 1023 (by norm_num) (by simpa using hy)

/-- A positive word whose exponent field is at least `e` has value at least `2 ^ (e - 1023)`. -/
theorem value_ge_of_exponent (y : UInt64) (e : Nat) (q : Int) (he : 1 ≤ e) (he' : e < 2048)
    (heq : (e : Int) = q + 1023) (hs : Wasm.IEEE64.sign y = false)
    (hye : e ≤ Wasm.IEEE64.exponent y) : (2 : ℝ) ^ q ≤ value y := by
  have hnn : 0 ≤ value y := by
    simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Int.cast_natCast]
    positivity
  have h := magnitude_ge y e q he he' heq hye
  rwa [abs_of_nonneg hnn] at h

/-- A word with value above `2 ^ -1022` is normal and positive. -/
theorem normal_of_value (y : UInt64) (hy : 1 / (2 : ℝ) ^ 1022 < value y) :
    1 ≤ Wasm.IEEE64.exponent y ∧ Wasm.IEEE64.sign y = false := by
  constructor
  · by_contra h
    have hm := magnitude_lt y 1 (-1022) le_rfl (by norm_num) (by omega)
    have hp : (2 : ℝ) ^ (-1022 : Int) = 1 / (2 : ℝ) ^ 1022 := by norm_num
    rw [hp] at hm
    have := le_abs_self (value y)
    linarith
  · by_contra h
    have hs : Wasm.IEEE64.sign y = true := by simpa using h
    have hv : value y ≤ 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
      have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude y : ℝ) / (2 : ℝ) ^ 1074 := by positivity
      rw [neg_div]
      linarith
    have : (0 : ℝ) < 1 / (2 : ℝ) ^ 1022 := by positivity
    linarith

theorem sum_scaled (a b : UInt64) :
    value a + value b =
      ((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : Int) : ℝ) / (2 : ℝ) ^ 1074 := by
  simp only [value]
  push_cast
  ring

theorem pow_div_1074 (n : Nat) : (2 : ℝ) ^ (1074 + n) / (2 : ℝ) ^ 1074 = 2 ^ n := by
  rw [pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ two_ne_zero)]

theorem scaled_ge (a b : UInt64) (n : Nat) (h : (2 : ℝ) ^ n ≤ value a + value b) :
    (2 : Int) ^ (1074 + n) ≤ Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
  rw [← pow_div_1074, sum_scaled, div_le_div_iff_of_pos_right (by positivity)] at h
  exact_mod_cast h

theorem scaled_lt (a b : UInt64) (n : Nat) (h : value a + value b < (2 : ℝ) ^ n) :
    Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < (2 : Int) ^ (1074 + n) := by
  rw [← pow_div_1074, sum_scaled, div_lt_div_iff_of_pos_right (by positivity)] at h
  exact_mod_cast h

/-- The value of a word whose scaled value is `R` multiples of `2 ^ g`. -/
theorem grid_value (w : UInt64) (R g : Nat)
    (h : Wasm.IEEE64.scaledValue w = (R : Int) * 2 ^ g) :
    value w = (R : ℝ) * (2 : ℝ) ^ g / (2 : ℝ) ^ 1074 := by
  rw [value, h, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]

/-- Half of `2 ^ g` scaled units is `2 ^ q u` when `g = q + 1022`. -/
theorem half_unit (g : Nat) (q : Int) (hq : (g : Int) = q + 1074 - 52) :
    (2 : ℝ) ^ g / 2 / (2 : ℝ) ^ 1074 = (2 : ℝ) ^ q * unitRoundoff64 := by
  have h := F64NearestBinade.power_quotient_split g 52 q hq
  rw [div_div, mul_comm (2 : ℝ), ← div_div, h]
  simp only [unitRoundoff64]
  ring

#print axioms value_zero
#print axioms value_zero_boundary
#print axioms negate_value
#print axioms sign_value
#print axioms normal_value
#print axioms positive_encoding_toNat
#print axioms lt_limit_of_finite
#print axioms finite_below_overflow
#print axioms magnitude_lt_of_exponent_lt
#print axioms magnitude_lt
#print axioms magnitude_ge
#print axioms exponent_ge_of_value
#print axioms exponent_ge_of_one_le
#print axioms value_ge_of_exponent
#print axioms normal_of_value
#print axioms sum_scaled
#print axioms pow_div_1074
#print axioms scaled_ge
#print axioms scaled_lt
#print axioms grid_value
/-- A word of nonzero value has a positive scaled magnitude. -/
theorem scaledMagnitude_pos (w : UInt64) (h : value w ≠ 0) :
    0 < Wasm.IEEE64.scaledMagnitude w := by
  rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude w) with h0 | h0
  · exfalso
    apply h
    simp only [value, Wasm.IEEE64.scaledValue, h0]
    split <;> simp
  · exact h0

#print axioms half_unit
#print axioms scaledMagnitude_pos

end LeanExe.ProofKit.F64Magnitude
