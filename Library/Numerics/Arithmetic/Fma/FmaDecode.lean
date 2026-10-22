import Library.Numerics.Arithmetic.Fma.FmaWords
import LeanExe.ProofKit.F64Exact

/-!
The fields of an operand as `Fma.fmaBits` decodes them, and the value of a finite operand.  A
finite word `x` with exponent field `e` and fraction field `f` has the significand `msig x`, which is
`f` for `e = 0` and `2 ^ 52 + f` otherwise, and the exponent `mexp x = max e 1`, so that its
magnitude is `msig x · 2 ^ (mexp x - 1)` units of `2 ^ -1074` (`magnitude_msig`).  The word
expressions of `fmaBits` compute these fields, the sign bits, and the tests for zeros and NaNs.
`product_value` writes `value a · value b` in units of `2 ^ -2400` as
`msig a · msig b · 2 ^ (mexp a + mexp b + 250)`, and `value_units` writes `value c` as
`msig c · 2 ^ (mexp c + 1325)`.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaDecode
open Library.Numerics.Arithmetic.Fma FmaWords CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- The significand of a word, with the hidden bit when the exponent field is nonzero. -/
def msig (x : UInt64) : ℕ :=
  if Wasm.IEEE64.exponent x = 0 then Wasm.IEEE64.fraction x else 2 ^ 52 + Wasm.IEEE64.fraction x

/-- The exponent of a word's grid: the exponent field, or 1 for a subnormal word. -/
def mexp (x : UInt64) : ℕ :=
  if Wasm.IEEE64.exponent x = 0 then 1 else Wasm.IEEE64.exponent x

theorem land_11 (n : ℕ) : n &&& 2047 = n % 2048 := Nat.and_two_pow_sub_one_eq_mod n 11

theorem land_52 (n : ℕ) : n &&& 4503599627370495 = n % 4503599627370496 :=
  Nat.and_two_pow_sub_one_eq_mod n 52

theorem fraction_lt (x : UInt64) : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by positivity)

theorem exponent_lt (x : UInt64) : Wasm.IEEE64.exponent x < 2048 := Nat.mod_lt _ (by positivity)

theorem exponent_bits (x : UInt64) :
    ((x >>> 52) &&& 0x7FF).toNat = Wasm.IEEE64.exponent x := by
  rw [UInt64.toNat_and, shr_toNat]
  have h1 : (52 : UInt64).toNat % 64 = 52 := rfl
  have h2 : (0x7FF : UInt64).toNat = 2047 := rfl
  rw [h1, h2, land_11]
  rfl

theorem fraction_bits (x : UInt64) :
    (x &&& 0xFFFFFFFFFFFFF).toNat = Wasm.IEEE64.fraction x := by
  rw [UInt64.toNat_and]
  have h : (0xFFFFFFFFFFFFF : UInt64).toNat = 4503599627370495 := rfl
  rw [h, land_52]
  rfl

theorem exponent_beq (x : UInt64) (k : UInt64) :
    ((x >>> 52) &&& 0x7FF == k) = decide (Wasm.IEEE64.exponent x = k.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, exponent_bits, decide_eq_true_iff]

theorem msig_bits (x : UInt64) :
    (if (x >>> 52) &&& 0x7FF == 0 then x &&& 0xFFFFFFFFFFFFF
      else (x &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000).toNat = msig x := by
  have hflt := fraction_lt x
  unfold msig
  rw [exponent_beq]
  by_cases h0 : Wasm.IEEE64.exponent x = 0
  · rw [ite_eq_left (by simpa using h0), ite_eq_left h0, fraction_bits]
  · rw [ite_eq_right (by simpa using h0), ite_eq_right h0, UInt64.toNat_or, fraction_bits]
    have h : (0x10000000000000 : UInt64).toNat = 2 ^ 52 := rfl
    have hor := Nat.two_pow_add_eq_or_of_lt hflt 1
    rw [mul_one] at hor
    rw [h, Nat.or_comm, ← hor]

theorem mexp_bits (x : UInt64) :
    (if (x >>> 52) &&& 0x7FF == 0 then (1 : UInt64) else (x >>> 52) &&& 0x7FF).toNat =
      mexp x := by
  unfold mexp
  rw [exponent_beq]
  by_cases h0 : Wasm.IEEE64.exponent x = 0
  · rw [ite_eq_left (by simpa using h0), ite_eq_left h0]
    rfl
  · rw [ite_eq_right (by simpa using h0), ite_eq_right h0, exponent_bits]

theorem magnitude_msig (x : UInt64) :
    Wasm.IEEE64.scaledMagnitude x = msig x * 2 ^ (mexp x - 1) := by
  unfold Wasm.IEEE64.scaledMagnitude msig mexp
  by_cases h0 : Wasm.IEEE64.exponent x = 0
  · simp [h0]
  · simp [h0]

theorem mexp_pos (x : UInt64) : 1 ≤ mexp x := by
  unfold mexp; split_ifs with h <;> omega

theorem msig_lt (x : UInt64) : msig x < 2 ^ 53 := by
  have := fraction_lt x
  unfold msig; split_ifs <;> simp only [Nat.reducePow] at * <;> omega

/-- A finite word has an exponent below 2047. -/
theorem mexp_le (x : UInt64) (hx : Finite x) : mexp x ≤ 2046 := by
  have h := exponent_lt x
  have hf : Wasm.IEEE64.exponent x ≠ 0x7FF := by
    simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hx
  unfold mexp; split_ifs <;> omega

theorem msig_pos (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) : 0 < msig x := by
  rw [magnitude_msig] at hx
  rcases Nat.eq_zero_or_pos (msig x) with h | h
  · rw [h, zero_mul] at hx; exact absurd rfl hx
  · exact h

theorem sign_bit (x : UInt64) : (x >>> 63).toNat = if Wasm.IEEE64.sign x then 1 else 0 := by
  have hx := x.toNat_lt
  rw [shr_toNat]
  have h1 : (63 : UInt64).toNat % 64 = 63 := rfl
  rw [h1]
  unfold Wasm.IEEE64.sign
  have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true h, ite_eq_left rfl]; omega
  · rw [decide_eq_false h, ite_eq_right Bool.false_ne_true]; omega

theorem sign_xor_bit (a b : UInt64) :
    ((a ^^^ b) >>> 63).toNat = if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then 1 else 0 := by
  have ha := sign_bit a
  have hb := sign_bit b
  rw [shr_toNat] at ha hb ⊢
  rw [UInt64.toNat_xor, Nat.xor_div_two_pow, ha, hb]
  cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl

theorem sign_bit_le (a : UInt64) : (a >>> 63).toNat ≤ 1 := by
  rw [sign_bit]; split_ifs <;> omega

theorem sign_xor_le (a b : UInt64) : ((a ^^^ b) >>> 63).toNat ≤ 1 := by
  rw [sign_xor_bit]; split_ifs <;> omega

theorem zero_bits (x : UInt64) :
    (x <<< 1 == 0) = decide (Wasm.IEEE64.scaledMagnitude x = 0) := by
  have hx := x.toNat_lt
  have hlow : (x <<< 1).toNat = x.toNat * 2 % 2 ^ 64 := by
    rw [shl_toNat]; rfl
  have hmag : Wasm.IEEE64.scaledMagnitude x = 0 ↔
      Wasm.IEEE64.exponent x = 0 ∧ Wasm.IEEE64.fraction x = 0 := by
    unfold Wasm.IEEE64.scaledMagnitude
    by_cases h0 : Wasm.IEEE64.exponent x = 0
    · simp [h0]
    · simp only [h0, beq_iff_eq, ite_false, false_and, iff_false]
      positivity
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, hlow, UInt64.toNat_zero,
    decide_eq_true_iff, hmag]
  unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  simp only [Nat.reducePow] at *
  omega

theorem nan_bits (x : UInt64) :
    ((x >>> 52) &&& 0x7FF == 0x7FF && x &&& 0xFFFFFFFFFFFFF != 0) = Wasm.IEEE64.isNaN x := by
  unfold Wasm.IEEE64.isNaN
  rw [exponent_beq]
  have hf : (x &&& 0xFFFFFFFFFFFFF != 0) = (Wasm.IEEE64.fraction x != 0) := by
    rw [Bool.eq_iff_iff, ne_zero_iff, fraction_bits, bne_iff_ne, ne_eq]
  rw [hf]
  rfl

/-- The value of a word in units of `2 ^ -2400`, with its sign. -/
theorem value_units (x : UInt64) :
    value x = (if Wasm.IEEE64.sign x then -1 else 1) *
      ((msig x * 2 ^ (mexp x + 1325) : ℕ) : ℝ) / 2 ^ 2400 := by
  have hm := mexp_pos x
  have hval : value x = (if Wasm.IEEE64.sign x then -1 else 1) *
      (Wasm.IEEE64.scaledMagnitude x : ℝ) / 2 ^ 1074 := by
    unfold value Wasm.IEEE64.scaledValue
    cases Wasm.IEEE64.sign x
    · simp
    · simp only [ite_true, Int.cast_neg, Int.cast_natCast]; ring
  rw [hval, magnitude_msig, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, show mexp x + 1325 = (mexp x - 1) + 1326 by omega, pow_add,
    show (2400 : ℕ) = 1074 + 1326 by norm_num, pow_add,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The product of two values in units of `2 ^ -2400`, with its sign. -/
theorem product_value (a b : UInt64) :
    value a * value b = (if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then -1 else 1) *
      ((msig a * msig b * 2 ^ (mexp a + mexp b + 250) : ℕ) : ℝ) / 2 ^ 2400 := by
  rw [value_units a, value_units b]
  have hs : ((if Wasm.IEEE64.sign a then -1 else 1) * (if Wasm.IEEE64.sign b then -1 else 1) : ℝ) =
      if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then -1 else 1 := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> norm_num
  rw [← hs]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_div_comm,
    ← mul_div_mul_right _ ((2 : ℝ) ^ 2400) (by positivity : (2 : ℝ) ^ 2400 ≠ 0),
    div_left_inj' (by positivity)]
  ring

#print axioms exponent_bits
#print axioms msig_bits
#print axioms mexp_bits
#print axioms magnitude_msig
#print axioms sign_xor_bit
#print axioms zero_bits
#print axioms nan_bits
#print axioms value_units
#print axioms product_value

end Library.Numerics.Arithmetic.Fma.FmaDecode
