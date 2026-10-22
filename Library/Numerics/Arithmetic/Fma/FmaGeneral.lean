import Library.Numerics.Arithmetic.Fma.FmaCombine

/-!
`Fma.fmaBits` on finite operands with nonzero `a` and `b`.  The exact `a · b + c` in units of
`2 ^ -2400` is `±P · 2 ^ wP ± C · 2 ^ wC` for the normalized product and addend of `FmaParts`
(`exact_product`, `exact_addend`).  When `c` is a zero, `fmaBits` rounds the product, which gives the signed
nearest-even reference of `a · b + c` (`general_product`).  Otherwise it returns `+0` for an exact
zero sum and the signed nearest-even reference of `a · b + c` for any other sum (`general_sum`).
-/

namespace Library.Numerics.Arithmetic.Fma.FmaGeneral
open Verified.Examples FmaWords FmaDecode FmaParts FmaCombine CodeLib.IEEE64 LeanExe.ProofKit

theorem finite_exponent (x : UInt64) (hx : Finite x) :
    ((x >>> 52) &&& 0x7FF == 0x7FF) = false := by
  rw [exponent_beq]
  have hf : Wasm.IEEE64.exponent x ≠ 0x7FF := by
    simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hx
  simpa using hf

theorem finite_not_nan (x : UInt64) (hx : Finite x) :
    ((x >>> 52) &&& 0x7FF == 0x7FF && x &&& 0xFFFFFFFFFFFFF != 0) = false := by
  rw [finite_exponent x hx, Bool.false_and]

theorem sgn_xor (a b : UInt64) :
    sgn ((a ^^^ b) >>> 63) = if Wasm.IEEE64.sign a != Wasm.IEEE64.sign b then -1 else 1 := by
  have h := sign_xor_bit a b
  unfold sgn
  by_cases hs : (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) = true
  · rw [ite_eq_left hs] at h ⊢
    rw [ite_eq_left (UInt64.toNat_inj.mp (by rw [h]; rfl))]
  · rw [ite_eq_right hs] at h ⊢
    rw [ite_eq_right (fun h' => by rw [h'] at h; exact absurd h (by decide))]

theorem sgn_sign (c : UInt64) :
    sgn (c >>> 63) = if Wasm.IEEE64.sign c then -1 else 1 := by
  have h := sign_bit c
  unfold sgn
  by_cases hs : Wasm.IEEE64.sign c = true
  · rw [ite_eq_left hs] at h ⊢
    rw [ite_eq_left (UInt64.toNat_inj.mp (by rw [h]; rfl))]
  · rw [ite_eq_right hs] at h ⊢
    rw [ite_eq_right (fun h' => by rw [h'] at h; exact absurd h (by decide))]

/-- The product `a · b` in units of `2 ^ -2400`, from the normalized product. -/
theorem exact_product (a b : UInt64) (S : ℕ)
    (hP : pair (product a b).1 (product a b).2.1 = msig a * msig b * 2 ^ S)
    (hw : (product a b).2.2.toNat + S = mexp a + mexp b + 250) :
    value a * value b = sgn ((a ^^^ b) >>> 63) *
      ((pair (product a b).1 (product a b).2.1 * 2 ^ (product a b).2.2.toNat : ℕ) : ℝ) /
        2 ^ 2400 := by
  have e : msig a * msig b * 2 ^ S * 2 ^ (product a b).2.2.toNat =
      msig a * msig b * 2 ^ (mexp a + mexp b + 250) := by
    rw [mul_assoc, ← pow_add, add_comm S, hw]
  rw [product_value, sgn_xor, hP, e]

/-- The addend `c` in units of `2 ^ -2400`, from the normalized addend. -/
theorem exact_addend (c : UInt64) (S : ℕ)
    (hC : pair (addend c).1 (addend c).2.1 = msig c * 2 ^ S)
    (hw : (addend c).2.2.toNat + S = mexp c + 1325) :
    value c = sgn (c >>> 63) *
      ((pair (addend c).1 (addend c).2.1 * 2 ^ (addend c).2.2.toNat : ℕ) : ℝ) / 2 ^ 2400 := by
  have e : msig c * 2 ^ S * 2 ^ (addend c).2.2.toNat = msig c * 2 ^ (mexp c + 1325) := by
    rw [mul_assoc, ← pow_add, add_comm S, hw]
  rw [value_units, sgn_sign, hC, e]

theorem value_zero_of (c : UInt64) (hc : Wasm.IEEE64.scaledMagnitude c = 0) : value c = 0 := by
  rw [value_units]
  have h : msig c = 0 := by
    rw [magnitude_msig] at hc
    rcases Nat.mul_eq_zero.mp hc with h | h
    · exact h
    · exact absurd h (by positivity)
  rw [h]
  simp

/-- `fmaBits` on finite operands with nonzero `a` and `b` reaches its general part. -/
theorem fmaBits_general (a b c : UInt64) (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    Fma.fmaBits a b c =
      if c <<< 1 == 0 then
        Fma.roundPack ((a ^^^ b) >>> 63) (product a b).2.2 (product a b).1 (product a b).2.1
      else
        combine ((a ^^^ b) >>> 63) (c >>> 63) (product a b).1 (product a b).2.1 (product a b).2.2
          (addend c).1 (addend c).2.1 (addend c).2.2 := by
  rw [fmaBits_eq, finite_not_nan a ha, finite_not_nan b hb, finite_not_nan c hc,
    finite_exponent a ha, finite_exponent b hb, finite_exponent c hc, zero_bits a, zero_bits b]
  simp only [Bool.false_eq_true, ite_false, Bool.false_or, Bool.or_false, decide_false, ha0,
    hb0]

/-- With `c` a zero, `fmaBits` rounds the product. -/
theorem general_product (a b c : UInt64) (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hc0 : Wasm.IEEE64.scaledMagnitude c = 0) :
    Fma.fmaBits a b c = F64SignedRounding.roundNearestEven (value a * value b + value c) := by
  rw [fmaBits_general a b c ha hb hc ha0 hb0, zero_bits c, ite_eq_left (by simpa using hc0)]
  obtain ⟨S, hP, hw, hP1, hP2, hP20, hw32⟩ := product_spec a b ha0 hb0 ha hb
  rw [value_zero_of c hc0, add_zero, exact_product a b S hP hw]
  have hpos : 0 < pair (product a b).1 (product a b).2.1 := lt_of_lt_of_le (by positivity) hP1
  refine round_sum _ _ _ _ (sign_xor_le a b) hw32 (pair (product a b).1 (product a b).2.1)
    (product a b).2.2.toNat 0 (by omega) (Nat.pos_iff_ne_zero.mp hpos)
    (lt_trans hP2 (by norm_num)) hpos ?_
  left
  simp

/-- With `c` nonzero, `fmaBits` returns `+0` for an exact zero sum and otherwise the signed
nearest-even reference of `a · b + c`. -/
theorem general_sum (a b c : UInt64) (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hc0 : Wasm.IEEE64.scaledMagnitude c ≠ 0) :
    Fma.fmaBits a b c = if value a * value b + value c = 0 then 0
      else F64SignedRounding.roundNearestEven (value a * value b + value c) := by
  rw [fmaBits_general a b c ha hb hc ha0 hb0, zero_bits c, ite_eq_right (by simpa using hc0)]
  obtain ⟨SP, hP, hwP, hP1, hP2, hP20, hwP32⟩ := product_spec a b ha0 hb0 ha hb
  obtain ⟨SC, hC, hwC, hC1, hC2, hC20, hwC32⟩ := addend_spec c hc0 hc
  rw [combine_spec _ _ _ _ _ _ _ _ (sign_xor_le a b) (sign_bit_le c) hP1 hP2 hP20 hC1 hC2 hC20
    hwP32 hwC32, exact_product a b SP hP hwP, exact_addend c SC hC hwC, ← add_div]
  have hu : (2 : ℝ) ^ 2400 ≠ 0 := by positivity
  by_cases hS : sgn ((a ^^^ b) >>> 63) *
      ((pair (product a b).1 (product a b).2.1 * 2 ^ (product a b).2.2.toNat : ℕ) : ℝ) +
      sgn (c >>> 63) * ((pair (addend c).1 (addend c).2.1 * 2 ^ (addend c).2.2.toNat : ℕ) : ℝ) = 0
  · rw [ite_eq_left hS, hS, zero_div, ite_eq_left rfl]
  · rw [ite_eq_right hS, ite_eq_right (div_ne_zero hS hu)]

#print axioms fmaBits_general
#print axioms general_product
#print axioms general_sum

end Library.Numerics.Arithmetic.Fma.FmaGeneral
