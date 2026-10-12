import Verified.Examples.StrconvRational
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64DivCore
import LeanExe.ProofKit.F64RoundDyadic
import LeanExe.ProofKit.F64GridExact

/-!
Lean's `Float.ofScientific` at `v4.34.0-rc2`, the meaning of every decimal literal of type `Float`,
is `round64` of the decimal (`ofScientific_spec`).  The definition takes Clinger's fast path when
`m < 2 ^ 53` and `e ≤ 22`: one multiplication or division of the exact double `m` by the exact
power of ten `10 ^ e` from `Float.exactlyRepresentablePowersOfTen`, which `F64Bits` turns into
Talos's `mul` and `div`, and `StrconvRational.dyadic64` and `rational64` into the reference.  Every
other input goes through `Float.Model.ofScientific`, which returns zero for `m = 0`, infinity for
`e > 2 ^ 11`, zero for `e < -(2 ^ 11 + log2 m)`, the model's product of `m · 2 ^ 52 · 2 ^ -52` and
`10 ^ e` for `e ≥ 0`, and its quotient of `m` by `10 ^ -e` otherwise.  ProofKit's
`F64RoundDyadic.pack_round_above_dyadic` and `F64DivCore.pack_div_finite` give the product and the
quotient as Talos's roundings, and the two saturated cases lie beyond the overflow threshold and
below half the least subnormal.
-/

namespace Verified.Examples.StrconvOfScientific
open StrconvGrid StrconvWords StrconvRational StrconvGrammar StrconvRound LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-! ### The reference at zero, below half a unit, and beyond the threshold -/

theorem refPos_small (f : Fmt) (y : ℝ) (hy : 0 ≤ y) (h : 2 * y < 1) : refPos f y = 0 := by
  have hR : RoundsTo f y 1 0 := by
    refine ⟨le_rfl, ?_, Or.inl rfl, ?_, ?_, ?_⟩
    · simp only [Nat.sub_self, pow_zero, mul_one]
      have : (1 : ℝ) ≤ 2 ^ f.p := one_le_pow₀ (by norm_num)
      linarith
    · simp; linarith
    · simp; linarith
    · intro ht; simp at ht; rcases ht with ht | ht <;> linarith
  rw [positive_reference f y 1 0 hR]
  unfold packInf StrconvGrid.pack
  have hF := f.hF
  have hL : 0 < limit f := by unfold limit; have := half_pos f; positivity
  rw [if_neg (by simp only [Nat.sub_self, zero_mul, zero_add]; omega)]
  simp

theorem refPos_large (f : Fmt) (y : ℝ) (h : threshold f ≤ y) : refPos f y = limit f := by
  unfold refPos; rw [if_pos h]

/-- `round64` of a nonnegative decimal is the word of the grid's reference. -/
theorem round64_pos (m : ℕ) (q : ℤ) :
    round64 (.dec false m q) = UInt64.ofNat (refPos b64 (m * (10 : ℝ) ^ q * 2 ^ 1074)) := by
  rw [round64_dec]; rfl

/-! ### The fast path -/

/-- The words of `Float.exactlyRepresentablePowersOfTen`. -/
theorem power_word (e : ℕ) (he : e ≤ 22) (h : e < Float.exactlyRepresentablePowersOfTen.size) :
    Wasm.IEEE64.isNaN (Float.exactlyRepresentablePowersOfTen[e]'h).toBits = false ∧
      Wasm.IEEE64.isInfinite (Float.exactlyRepresentablePowersOfTen[e]'h).toBits = false ∧
      Wasm.IEEE64.sign (Float.exactlyRepresentablePowersOfTen[e]'h).toBits = false ∧
      Wasm.IEEE64.scaledMagnitude (Float.exactlyRepresentablePowersOfTen[e]'h).toBits =
        10 ^ e * 2 ^ 1074 := by
  interval_cases e <;>
    simp only [Float.exactlyRepresentablePowersOfTen, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero, F64Bits.toBits_ofBits] <;> decide +kernel

/-- The word of an exact integer below `2 ^ 53`. -/
theorem int_word (m : ℕ) (hm : m < 2 ^ 53) :
    Wasm.IEEE64.isNaN (Wasm.IEEE64.convertI64U m.toUInt64) = false ∧
      Wasm.IEEE64.isInfinite (Wasm.IEEE64.convertI64U m.toUInt64) = false ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.convertI64U m.toUInt64) = false ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.convertI64U m.toUInt64) = m * 2 ^ 1074 := by
  have hm64 : m.toUInt64.toNat = m := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)]
  have hc : Wasm.IEEE64.convertI64U m.toUInt64 =
      Wasm.IEEE64.roundScaledMagnitude ((m : ℤ) < 0) ((m : ℤ).natAbs * 2 ^ 1074) := by
    simp [Wasm.IEEE64.convertI64U, Wasm.IEEE64.fromInt, hm64]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [hc]
    simp only [Nat.cast_zero, lt_self_iff_false, decide_false, Int.natAbs_zero, zero_mul]
    decide
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact (m : ℤ) 1074
    (by simp; omega) (by norm_num)
  rw [← hc] at hf hv
  generalize Wasm.IEEE64.convertI64U m.toUInt64 = w at hf hv ⊢
  have hs : Wasm.IEEE64.sign w = false := by
    by_contra hs
    simp only [Bool.not_eq_false] at hs
    simp only [Wasm.IEEE64.scaledValue, hs, ite_true] at hv
    have h1 : (0 : ℤ) < m * 2 ^ 1074 := by positivity
    have h2 : (0 : ℤ) ≤ (Wasm.IEEE64.scaledMagnitude w : ℤ) := by positivity
    omega
  refine ⟨CodeLib.IEEE64.not_nan_of_finite hf, CodeLib.IEEE64.not_infinite_of_finite hf, hs, ?_⟩
  simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false] at hv
  exact_mod_cast hv

#print axioms power_word
#print axioms int_word

theorem ref_zero (q : ℤ) : UInt64.ofNat (refPos b64 ((0 : ℕ) * (10 : ℝ) ^ q * 2 ^ 1074)) = 0 := by
  rw [refPos_small b64 _ (by simp) (by simp)]; rfl

/-- The fast path's division of `m` by `10 ^ e`. -/
theorem fast_div (m e : ℕ) (hm : m < 2 ^ 53) (he : e ≤ 22)
    (h : e < Float.exactlyRepresentablePowersOfTen.size) :
    (m.toUInt64.toFloat / Float.exactlyRepresentablePowersOfTen[e]'h).toBits =
      UInt64.ofNat (refPos b64 (m * (10 : ℝ) ^ (-(e : ℤ)) * 2 ^ 1074)) := by
  rw [F64Bits.toBits_div, F64Convert.toBits_toFloat]
  obtain ⟨a1, a2, a3, a4⟩ := int_word m hm
  obtain ⟨b1, b2, b3, b4⟩ := power_word e he h
  generalize Wasm.IEEE64.convertI64U m.toUInt64 = a at a1 a2 a3 a4
  generalize (Float.exactlyRepresentablePowersOfTen[e]'h).toBits = b at b1 b2 b3 b4
  have hP : (0 : ℕ) < 2 ^ 1074 := by positivity
  have hPr : ((2 ^ 1074 : ℕ) : ℝ) = (2 : ℝ) ^ 1074 := by push_cast; ring
  rw [← hPr]
  generalize hPd : 2 ^ 1074 = P at a4 b4 hP hPr ⊢
  have hb0 : (10 ^ e * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [refPos_small b64 _ (by simp) (by simp)]
    simp only [Wasm.IEEE64.div, a1, a2, a3, a4, b1, b2, b3, b4, hb0, Bool.or_self,
      Bool.false_eq_true, ite_false, zero_mul, beq_self_eq_true, ite_true, bne_self_eq_false]
    rfl
  · have ha0 : (m * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
    simp only [Wasm.IEEE64.div, a1, a2, a3, a4, b1, b2, b3, b4, hb0, ha0, Bool.or_self,
      Bool.false_eq_true, ite_false, bne_self_eq_false]
    rw [hPd, rational64 _ _ (by positivity) (by positivity)]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    have key : ((m * P * P : ℕ) : ℝ) / ((10 ^ e * P : ℕ) : ℝ) =
        (m : ℝ) * (10 : ℝ) ^ (-(e : ℤ)) * P := by
      rw [zpow_neg, zpow_natCast]; push_cast; field_simp
    rw [key]

/-- The fast path's product of `m` and `10 ^ e`. -/
theorem fast_mul (m e : ℕ) (hm : m < 2 ^ 53) (he : e ≤ 22)
    (h : e < Float.exactlyRepresentablePowersOfTen.size) :
    (m.toUInt64.toFloat * Float.exactlyRepresentablePowersOfTen[e]'h).toBits =
      UInt64.ofNat (refPos b64 (m * (10 : ℝ) ^ (e : ℤ) * 2 ^ 1074)) := by
  rw [F64Bits.toBits_mul, F64Convert.toBits_toFloat]
  obtain ⟨a1, a2, a3, a4⟩ := int_word m hm
  obtain ⟨b1, b2, b3, b4⟩ := power_word e he h
  generalize Wasm.IEEE64.convertI64U m.toUInt64 = a at a1 a2 a3 a4
  generalize (Float.exactlyRepresentablePowersOfTen[e]'h).toBits = b at b1 b2 b3 b4
  have hP : (0 : ℕ) < 2 ^ 1074 := by positivity
  have hPr : ((2 ^ 1074 : ℕ) : ℝ) = (2 : ℝ) ^ 1074 := by push_cast; ring
  rw [← hPr]
  generalize hPd : 2 ^ 1074 = P at a4 b4 hP hPr ⊢
  have hb0 : (10 ^ e * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [refPos_small b64 _ (by simp) (by simp)]
    simp only [Wasm.IEEE64.mul, a1, a2, a3, a4, b1, b2, b3, b4, hb0, Bool.or_self,
      Bool.false_eq_true, ite_false, zero_mul, beq_self_eq_true, ite_true, Bool.true_or,
      bne_self_eq_false]
    rfl
  · have ha0 : (m * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
    simp only [Wasm.IEEE64.mul, a1, a2, a3, a4, b1, b2, b3, b4, hb0, ha0, Bool.or_self,
      Bool.false_eq_true, ite_false, bne_self_eq_false]
    rw [dyadic64 _ _ (by positivity)]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    have key : ((m * P * (10 ^ e * P) : ℕ) : ℝ) / (2 : ℝ) ^ 1074 =
        (m : ℝ) * (10 : ℝ) ^ (e : ℤ) * P := by
      rw [← hPr, zpow_natCast]; push_cast; field_simp
    rw [key]

open Float.Model in
/-- The model's product of two positive finite values whose exponent sum lies at or below the
target exponent of the product is Talos's dyadic rounding. -/
theorem pack_mul_finite (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (he : -1074 ≤ e₁ + e₂)
    (ht : e₁ + e₂ ≤ Format.binary64.targetExponent (totalExponent (m₁ * m₂) (e₁ + e₂))) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.mul Format.binary64
      (.finite .positive m₁ e₁ h₁) (.finite .positive m₂ e₂ h₂))) =
      Wasm.IEEE64.roundDyadicMagnitude false (m₁ * m₂ * 2 ^ (e₁ + e₂ + 1074).toNat) 0 := by
  have hd : (e₁ + e₂ - Format.binary64.targetExponent
      (totalExponent (m₁ * m₂) (e₁ + e₂))).toNat = 0 := by omega
  have hr : UnpackedFloat.round Format.binary64 (.positive * .positive) (m₁ * m₂) (e₁ + e₂) =
      UnpackedFloat.roundWithAccuracy Format.binary64 (.positive * .positive) (m₁ * m₂)
        (e₁ + e₂) .exact := by
    simp [UnpackedFloat.round, UnpackedFloat.decreaseExponent, hd]
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.roundWithAccuracy Format.binary64 (.positive * .positive) (m₁ * m₂)
      (e₁ + e₂) .exact)) = _
  rw [← hr, F64RoundDyadic.pack_round_above_dyadic _ _ 0 _ (by positivity) (by omega)]
  simp only [Nat.cast_zero, add_zero]
  rfl

open Float.Model in
/-- The model's path. -/
theorem slow_path (m : ℕ) (q : ℤ) :
    (Float.ofModel (Float.Model.ofScientific m q)).toBits =
      UInt64.ofNat (refPos b64 (m * (10 : ℝ) ^ q * 2 ^ 1074)) := by
  show UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.ofScientific Format.binary64 m q)) = _
  have hmb : Format.binary64.mantissaBits = 53 := rfl
  have heb : Format.binary64.exponentBits = 11 := rfl
  unfold UnpackedFloat.ofScientific
  split_ifs with h0 h1 h2 h3
  · subst h0
    rw [F64Packing.pack_zero, refPos_small b64 _ (by simp) (by simp)]
    rfl
  · -- beyond the exponents: infinity
    rw [F64Packing.pack_infinity, refPos_large]
    · show Wasm.IEEE64.infinity false = _
      rw [infinity64]
    · rw [heb] at h1
      have hq : (2049 : ℤ) ≤ q := by omega
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have h10 : (10 : ℝ) ^ (2049 : ℤ) ≤ 10 ^ q := zpow_le_zpow_right₀ (by norm_num) hq
      have h2049 : (2 : ℝ) ^ 2049 ≤ 10 ^ (2049 : ℤ) := by
        rw [show (2049 : ℤ) = ((2049 : ℕ) : ℤ) from rfl, zpow_natCast]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have ht : threshold b64 ≤ (2 : ℝ) ^ 2049 * 2 ^ 1074 := by
        unfold threshold; simp only [b64]; norm_num
      have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
      calc threshold b64 ≤ (2 : ℝ) ^ 2049 * 2 ^ 1074 := ht
        _ ≤ 10 ^ q * 2 ^ 1074 := by nlinarith
        _ ≤ m * 10 ^ q * 2 ^ 1074 := by
          have : (0 : ℝ) < 10 ^ q * 2 ^ 1074 := by positivity
          nlinarith
  · -- below the exponents: zero
    rw [heb] at h2
    rw [F64Packing.pack_zero]
    have hlt : 2 * ((m : ℝ) * 10 ^ q * 2 ^ 1074) < 1 := by
      set L := Nat.log2 m
      have hq : q ≤ -(2049 + (L : ℤ)) := by omega
      have hmL : (m : ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_log2_self
      have h10 : (10 : ℝ) ^ q ≤ 10 ^ (-(2049 + (L : ℤ))) := zpow_le_zpow_right₀ (by norm_num) hq
      have h2' : (10 : ℝ) ^ (-(2049 + (L : ℤ))) ≤ 2 ^ (-(2049 + (L : ℤ))) := by
        rw [zpow_neg, zpow_neg]
        apply inv_anti₀ (by positivity)
        rw [show (2049 + (L : ℤ)) = ((2049 + L : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have hprod : (2 : ℝ) ^ (L + 1) * 2 ^ (-(2049 + (L : ℤ))) * 2 ^ 1074 = 2 ^ (-974 : ℤ) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num),
          ← zpow_add₀ (by norm_num)]
        congr 1; push_cast; ring
      have hsmall : (2 : ℝ) ^ (-974 : ℤ) < 1 / 2 := by
        rw [zpow_neg]; norm_num
      have : (m : ℝ) * 10 ^ q * 2 ^ 1074 < 1 / 2 := by
        calc (m : ℝ) * 10 ^ q * 2 ^ 1074 ≤ 2 ^ (L + 1) * 10 ^ q * 2 ^ 1074 := by
              gcongr
          _ ≤ 2 ^ (L + 1) * 2 ^ (-(2049 + (L : ℤ))) * 2 ^ 1074 := by
              gcongr; exact h10.trans h2'
          _ = 2 ^ (-974 : ℤ) := hprod
          _ < 1 / 2 := hsmall
      linarith
    rw [refPos_small b64 _ (by positivity) hlt]
    rfl
  · -- the product
    have hm0 : 0 < m := Nat.pos_of_ne_zero h0
    rw [pack_mul_finite]
    · rw [dyadic64 _ _ (by rw [hmb, Nat.shiftLeft_eq]; positivity)]
      have hq0 : (q.toNat : ℤ) = q := Int.toNat_of_nonneg h3
      have hx : (-((53 : ℕ) : ℤ) + 0 + 1074).toNat = 1021 := by decide
      rw [hmb, Nat.shiftLeft_eq, hx]
      have key : ((m * 2 ^ 53 * 10 ^ q.toNat * 2 ^ 1021 : ℕ) : ℝ) / (2 : ℝ) ^ 0 =
          (m : ℝ) * (10 : ℝ) ^ q * 2 ^ 1074 := by
        rw [← hq0, zpow_natCast, Int.toNat_natCast, pow_zero, div_one]
        push_cast
        rw [show (2 : ℝ) ^ 1074 = 2 ^ 53 * 2 ^ 1021 by rw [← pow_add]]
        ring
      rw [key]
    · rw [hmb]; norm_num
    · rw [hmb]
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
      have hM0 : m <<< 53 * 10 ^ q.toNat ≠ 0 := by rw [Nat.shiftLeft_eq]; positivity
      have hlog : 53 ≤ Nat.log2 (m <<< 53 * 10 ^ q.toNat) := by
        rw [Nat.le_log2 hM0, Nat.shiftLeft_eq]
        calc 2 ^ 53 = 1 * 2 ^ 53 * 1 := by ring
          _ ≤ m * 2 ^ 53 * 10 ^ q.toNat :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hm0) (Nat.one_le_pow _ _ (by norm_num))
      have : (53 : ℤ) ≤ (Nat.log2 (m <<< 53 * 10 ^ q.toNat) : ℤ) := by exact_mod_cast hlog
      norm_num
      omega
  · -- the quotient
    have hm0 : 0 < m := Nat.pos_of_ne_zero h0
    rw [F64DivCore.pack_div_finite]
    · rw [show FloatCommon.negative (UnpackedFloat.Sign.positive / UnpackedFloat.Sign.positive) =
          false from rfl, rational64 _ _ (by positivity) (by positivity)]
      have hq0 : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      have hx : ((0 : ℤ) + 1074).toNat = 1074 := by decide
      rw [hx]
      have key : ((m * 2 ^ 1074 * 2 ^ 1074 : ℕ) : ℝ) / ((10 ^ (-q).toNat * 2 ^ 1074 : ℕ) : ℝ) =
          (m : ℝ) * (10 : ℝ) ^ q * 2 ^ 1074 := by
        have e1 : (10 : ℝ) ^ q = ((10 : ℝ) ^ (-q).toNat)⁻¹ := by
          rw [← zpow_natCast, hq0, zpow_neg, inv_inv]
        rw [e1]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        have h2 : (2 : ℝ) ^ 1074 ≠ 0 := by positivity
        have h10 : (10 : ℝ) ^ (-q).toNat ≠ 0 := by positivity
        field_simp
      rw [key]
    · norm_num
    · norm_num

/-- Lean's `Float.ofScientific`, the meaning of a decimal literal of type `Float`, is the
binary64 word of roundTiesToEven applied to `m · 10 ^ (±e)`. -/
theorem ofScientific_spec (m : ℕ) (s : Bool) (e : ℕ) :
    (Float.ofScientific m s e).toBits = round64 (.dec false m (if s then -(e : ℤ) else e)) := by
  rw [round64_pos]
  unfold Float.ofScientific
  split
  · rename_i h
    cases s
    · simp only [Bool.false_eq_true, ite_false]
      exact fast_mul m e h.1 h.2 _
    · simp only [ite_true]
      exact fast_div m e h.1 h.2 _
  · cases s
    · simp only [Bool.false_eq_true, ite_false]
      exact slow_path m e
    · simp only [ite_true, Int.negOfNat_eq]
      exact slow_path m (-(e : ℤ))

#print axioms fast_div
#print axioms fast_mul
#print axioms slow_path
#print axioms ofScientific_spec

end Verified.Examples.StrconvOfScientific
