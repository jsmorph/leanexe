import Library.Numerics.Decimal.Shared.StrconvOfScientific
import LeanExe.ProofKit.F32Bits
import LeanExe.ProofKit.F32Convert
import LeanExe.ProofKit.F32DivCore
import LeanExe.ProofKit.F32RoundDyadic

/-!
Lean's `Float32.ofScientific` at `v4.34.0-rc2`, the meaning of every decimal literal of type
`Float32`, is `round32` of the decimal (`ofScientific32_spec`).  The proof follows
`StrconvOfScientific`: the fast path, for `m < 2 ^ 23` and `e ≤ 10`, is one binary32
multiplication or division of exact values, and the model's path is a rounded product or quotient,
with the saturated cases beyond `e > 2 ^ 8` and below `e < -(2 ^ 8 + log2 m)`.  The exact binary32
value of an integer `m < 2 ^ 24` comes from the grid: `roundScaledMagnitude` is the dyadic rounding
with no fraction bits, and `m · 2 ^ 149` is the exact grid point `Q · 2 ^ (E - 1)` with
`Q = m · 2 ^ (23 - log2 m)` (`exact_word`).
-/

namespace Library.Numerics.Decimal.Shared.StrconvOfScientific32
open StrconvGrid StrconvWords StrconvRational StrconvRound StrconvOfScientific LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `round32` of a nonnegative decimal is the word of the grid's reference. -/
theorem round32_pos (m : ℕ) (q : ℤ) :
    round32 (.dec false m q) = UInt32.ofNat (refPos b32 (m * (10 : ℝ) ^ q * 2 ^ 149)) := by
  rw [round32_dec]; rfl

/-- An exact grid point rounds to its own encoding. -/
theorem roundsTo_exact (f : Fmt) (E Q : ℕ) (hE : 1 ≤ E) (hQ : Q < 2 ^ f.p)
    (hQ1 : E = 1 ∨ 2 ^ (f.p - 1) ≤ Q) : RoundsTo f ((Q : ℝ) * 2 ^ (E - 1)) E Q := by
  have hS : (0 : ℝ) < 2 ^ (E - 1) := by positivity
  refine ⟨hE, ?_, ?_, ?_, ?_, ?_⟩
  · have : (Q : ℝ) < 2 ^ f.p := by exact_mod_cast hQ
    nlinarith
  · rcases hQ1 with h | h
    · exact Or.inl h
    · right
      have : (2 : ℝ) ^ (f.p - 1) ≤ Q := by exact_mod_cast h
      nlinarith
  · nlinarith
  · nlinarith
  · intro h; rcases h with h | h <;> nlinarith

theorem scaled_dyadic32 (n : ℕ) (hn : 0 < n) :
    Wasm.IEEE32.roundScaledMagnitude false n = Wasm.IEEE32.roundDyadicMagnitude false n 0 := by
  have hn0 : (n == 0) = false := by simpa using hn.ne'
  unfold Wasm.IEEE32.roundDyadicMagnitude
  simp only [hn0, Bool.false_eq_true, ite_false, zero_add, beq_self_eq_true, ite_true]
  by_cases hs : Nat.log2 n - 23 = 0
  · simp [hs]
  · have hs' : (Nat.log2 n - 23 == 0) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ite_false]
    have hbig : 2 ^ 24 ≤ n := by
      have h0 : n ≠ 0 := by omega
      exact (Nat.le_log2 h0).mp (by omega)
    unfold Wasm.IEEE32.roundScaledMagnitude
    rw [if_neg (by omega), if_neg (by omega)]

/-- The binary32 word of an integer below `2 ^ 24` is exact. -/
theorem exact_word (m : ℕ) (hm0 : 0 < m) (hm : m < 2 ^ 24) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.fromInt m) = false ∧
      Wasm.IEEE32.isInfinite (Wasm.IEEE32.fromInt m) = false ∧
      Wasm.IEEE32.sign (Wasm.IEEE32.fromInt m) = false ∧
      Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.fromInt m) = m * 2 ^ 149 := by
  set L := Nat.log2 m with hL
  have hm00 : m ≠ 0 := by omega
  have hL23 : L ≤ 23 := by
    have := (Nat.log2_lt hm00).mpr hm; omega
  have hL1 := Nat.log2_self_le hm00
  have hL2 := Nat.lt_log2_self (n := m)
  set Q := m * 2 ^ (23 - L) with hQ
  have hQlo : 2 ^ 23 ≤ Q := by
    rw [hQ, show (2 : ℕ) ^ 23 = 2 ^ L * 2 ^ (23 - L) by rw [← pow_add]; congr 1; omega]
    exact Nat.mul_le_mul_right _ hL1
  have hQhi : Q < 2 ^ 24 := by
    rw [hQ, show (2 : ℕ) ^ 24 = 2 ^ (L + 1) * 2 ^ (23 - L) by rw [← pow_add]; congr 1; omega]
    exact Nat.mul_lt_mul_of_pos_right hL2 (by positivity)
  have hval : m * 2 ^ 149 = Q * 2 ^ (127 + L - 1) := by
    rw [hQ, mul_assoc, ← pow_add]; congr 2; omega
  have hRT := roundsTo_exact b32 (127 + L) Q (by omega) (by simpa [b32] using hQhi)
    (Or.inr (by simpa [b32] using hQlo))
  have href := positive_reference b32 _ _ _ hRT
  have hpack : packInf b32 (127 + L) Q = pack b32 (127 + L) Q := by
    unfold packInf
    rw [if_neg]
    rw [limit_b32]; unfold pack; rw [half_b32]
    simp only [b32, not_or, not_le]
    omega
  have hlim : pack b32 (127 + L) Q < limit b32 := by
    rw [limit_b32]; unfold pack; rw [half_b32]; omega
  have hw : Wasm.IEEE32.fromInt m = UInt32.ofNat (pack b32 (127 + L) Q) := by
    unfold Wasm.IEEE32.fromInt
    have hd : decide ((m : ℤ) < 0) = false := by simp
    rw [hd, Int.natAbs_natCast]
    rw [scaled_dyadic32 _ (by positivity), dyadic32 _ _ (by positivity), pow_zero, div_one,
      ← hpack, ← href]
    congr 2
    rw [hval]; push_cast; ring
  rw [hw]
  have hn := toNat32 _ hlim
  rw [limit_b32] at hlim
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Wasm.IEEE32.isNaN, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, hn]
    have : ¬ (pack b32 (127 + L) Q / 8388608 % 256 = 255) := by omega
    simp [this]
  · simp only [Wasm.IEEE32.isInfinite, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, hn]
    have : ¬ (pack b32 (127 + L) Q / 8388608 % 256 = 255) := by omega
    simp [this]
  · simp only [Wasm.IEEE32.sign, hn, decide_eq_false_iff_not, not_le]; omega
  · rw [scaledMagnitude32 _ (by rw [limit_b32]; exact hlim),
      mag_pack b32 _ _ (by omega) (by rw [half_b32]; omega) (Or.inr (by rw [half_b32]; exact hQlo)),
      hval]

/-- The words of `Float32.exactlyRepresentablePowersOfTen`. -/
theorem power_word32 (e : ℕ) (he : e ≤ 10) (h : e < Float32.exactlyRepresentablePowersOfTen.size) :
    Wasm.IEEE32.isNaN (Float32.exactlyRepresentablePowersOfTen[e]'h).toBits = false ∧
      Wasm.IEEE32.isInfinite (Float32.exactlyRepresentablePowersOfTen[e]'h).toBits = false ∧
      Wasm.IEEE32.sign (Float32.exactlyRepresentablePowersOfTen[e]'h).toBits = false ∧
      Wasm.IEEE32.scaledMagnitude (Float32.exactlyRepresentablePowersOfTen[e]'h).toBits =
        10 ^ e * 2 ^ 149 := by
  interval_cases e <;>
    simp only [Float32.exactlyRepresentablePowersOfTen, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero, F32Bits.toBits_ofBits] <;> decide +kernel

theorem toFloat32_bits (m : ℕ) (hm : m < 2 ^ 64) :
    (m.toUInt64.toFloat32).toBits = Wasm.IEEE32.fromInt m := by
  have hm64 : m.toUInt64.toNat = m := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)]
  change (Float32.Model.ofInt (m.toUInt64.toNat : ℤ)).toBits = _
  rw [F32Convert.ofInt_eq, hm64]

theorem int_word32 (m : ℕ) (hm : m < 2 ^ 23) :
    Wasm.IEEE32.isNaN (m.toUInt64.toFloat32).toBits = false ∧
      Wasm.IEEE32.isInfinite (m.toUInt64.toFloat32).toBits = false ∧
      Wasm.IEEE32.sign (m.toUInt64.toFloat32).toBits = false ∧
      Wasm.IEEE32.scaledMagnitude (m.toUInt64.toFloat32).toBits = m * 2 ^ 149 := by
  rw [toFloat32_bits m (by omega)]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp only [Wasm.IEEE32.fromInt, Nat.cast_zero, lt_self_iff_false, decide_false,
      Int.natAbs_zero, zero_mul]
    decide
  · exact exact_word m hpos (by omega)

theorem ref_zero32 (q : ℤ) : UInt32.ofNat (refPos b32 ((0 : ℕ) * (10 : ℝ) ^ q * 2 ^ 149)) = 0 := by
  rw [refPos_small b32 _ (by simp) (by simp)]; rfl

theorem fast_div32 (m e : ℕ) (hm : m < 2 ^ 23) (he : e ≤ 10)
    (h : e < Float32.exactlyRepresentablePowersOfTen.size) :
    (m.toUInt64.toFloat32 / Float32.exactlyRepresentablePowersOfTen[e]'h).toBits =
      UInt32.ofNat (refPos b32 (m * (10 : ℝ) ^ (-(e : ℤ)) * 2 ^ 149)) := by
  rw [F32Bits.toBits_div]
  obtain ⟨a1, a2, a3, a4⟩ := int_word32 m hm
  obtain ⟨b1, b2, b3, b4⟩ := power_word32 e he h
  generalize (m.toUInt64.toFloat32).toBits = a at a1 a2 a3 a4
  generalize (Float32.exactlyRepresentablePowersOfTen[e]'h).toBits = b at b1 b2 b3 b4
  have hP : (0 : ℕ) < 2 ^ 149 := by positivity
  have hPr : ((2 ^ 149 : ℕ) : ℝ) = (2 : ℝ) ^ 149 := by push_cast; ring
  rw [← hPr]
  generalize hPd : 2 ^ 149 = P at a4 b4 hP hPr ⊢
  have hb0 : (10 ^ e * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [refPos_small b32 _ (by simp) (by simp)]
    simp only [Wasm.IEEE32.div, a1, a2, a3, a4, b1, b2, b3, b4, hb0, Bool.or_self,
      Bool.false_eq_true, ite_false, zero_mul, beq_self_eq_true, ite_true, bne_self_eq_false]
    rfl
  · have ha0 : (m * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
    simp only [Wasm.IEEE32.div, a1, a2, a3, a4, b1, b2, b3, b4, hb0, ha0, Bool.or_self,
      Bool.false_eq_true, ite_false, bne_self_eq_false]
    rw [hPd, rational32 _ _ (by positivity) (by positivity)]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    have key : ((m * P * P : ℕ) : ℝ) / ((10 ^ e * P : ℕ) : ℝ) =
        (m : ℝ) * (10 : ℝ) ^ (-(e : ℤ)) * P := by
      rw [zpow_neg, zpow_natCast]; push_cast; field_simp
    rw [key]

theorem fast_mul32 (m e : ℕ) (hm : m < 2 ^ 23) (he : e ≤ 10)
    (h : e < Float32.exactlyRepresentablePowersOfTen.size) :
    (m.toUInt64.toFloat32 * Float32.exactlyRepresentablePowersOfTen[e]'h).toBits =
      UInt32.ofNat (refPos b32 (m * (10 : ℝ) ^ (e : ℤ) * 2 ^ 149)) := by
  rw [F32Bits.toBits_mul]
  obtain ⟨a1, a2, a3, a4⟩ := int_word32 m hm
  obtain ⟨b1, b2, b3, b4⟩ := power_word32 e he h
  generalize (m.toUInt64.toFloat32).toBits = a at a1 a2 a3 a4
  generalize (Float32.exactlyRepresentablePowersOfTen[e]'h).toBits = b at b1 b2 b3 b4
  have hP : (0 : ℕ) < 2 ^ 149 := by positivity
  have hPr : ((2 ^ 149 : ℕ) : ℝ) = (2 : ℝ) ^ 149 := by push_cast; ring
  rw [← hPr]
  generalize hPd : 2 ^ 149 = P at a4 b4 hP hPr ⊢
  have hb0 : (10 ^ e * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [refPos_small b32 _ (by simp) (by simp)]
    simp only [Wasm.IEEE32.mul, a1, a2, a3, a4, b1, b2, b3, b4, hb0, Bool.or_self,
      Bool.false_eq_true, ite_false, zero_mul, beq_self_eq_true, ite_true, Bool.true_or,
      bne_self_eq_false]
    rfl
  · have ha0 : (m * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
    simp only [Wasm.IEEE32.mul, a1, a2, a3, a4, b1, b2, b3, b4, hb0, ha0, Bool.or_self,
      Bool.false_eq_true, ite_false, bne_self_eq_false]
    rw [dyadic32 _ _ (by positivity)]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    have key : ((m * P * (10 ^ e * P) : ℕ) : ℝ) / (2 : ℝ) ^ 149 =
        (m : ℝ) * (10 : ℝ) ^ (e : ℤ) * P := by
      rw [← hPr, zpow_natCast]; push_cast; field_simp
    rw [key]

open Float.Model in
theorem pack_mul_finite32 (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (he : -149 ≤ e₁ + e₂)
    (ht : e₁ + e₂ ≤ Format.binary32.targetExponent (totalExponent (m₁ * m₂) (e₁ + e₂))) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (UnpackedFloat.mul Format.binary32
      (.finite .positive m₁ e₁ h₁) (.finite .positive m₂ e₂ h₂))) =
      Wasm.IEEE32.roundDyadicMagnitude false (m₁ * m₂ * 2 ^ (e₁ + e₂ + 149).toNat) 0 := by
  have hd : (e₁ + e₂ - Format.binary32.targetExponent
      (totalExponent (m₁ * m₂) (e₁ + e₂))).toNat = 0 := by omega
  have hr : UnpackedFloat.round Format.binary32 (.positive * .positive) (m₁ * m₂) (e₁ + e₂) =
      UnpackedFloat.roundWithAccuracy Format.binary32 (.positive * .positive) (m₁ * m₂)
        (e₁ + e₂) .exact := by
    simp [UnpackedFloat.round, UnpackedFloat.decreaseExponent, hd]
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (UnpackedFloat.roundWithAccuracy Format.binary32 (.positive * .positive) (m₁ * m₂)
      (e₁ + e₂) .exact)) = _
  rw [← hr, F32RoundDyadic.pack_round_above_dyadic _ _ 0 _ (by positivity) (by omega)]
  simp only [Nat.cast_zero, add_zero]
  rfl

theorem infinity32' : Wasm.IEEE32.infinity false = UInt32.ofNat (limit b32) := infinity32

open Float.Model in
theorem slow_path32 (m : ℕ) (q : ℤ) :
    (Float32.ofModel (Float32.Model.ofScientific m q)).toBits =
      UInt32.ofNat (refPos b32 (m * (10 : ℝ) ^ q * 2 ^ 149)) := by
  show UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (UnpackedFloat.ofScientific Format.binary32 m q)) = _
  have hmb : Format.binary32.mantissaBits = 24 := rfl
  have heb : Format.binary32.exponentBits = 8 := rfl
  unfold UnpackedFloat.ofScientific
  split_ifs with h0 h1 h2 h3
  · subst h0
    rw [F32Packing.pack_zero, refPos_small b32 _ (by simp) (by simp)]
    rfl
  · rw [F32Packing.pack_infinity, refPos_large]
    · show Wasm.IEEE32.infinity false = _
      rw [infinity32]
    · rw [heb] at h1
      have hq : (257 : ℤ) ≤ q := by omega
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have h10 : (10 : ℝ) ^ (257 : ℤ) ≤ 10 ^ q := zpow_le_zpow_right₀ (by norm_num) hq
      have h257 : (2 : ℝ) ^ 257 ≤ 10 ^ (257 : ℤ) := by
        rw [show (257 : ℤ) = ((257 : ℕ) : ℤ) from rfl, zpow_natCast]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have ht : threshold b32 ≤ (2 : ℝ) ^ 257 * 2 ^ 149 := by
        unfold threshold; simp only [b32]; norm_num
      have hp : (0 : ℝ) < 2 ^ 149 := by positivity
      calc threshold b32 ≤ (2 : ℝ) ^ 257 * 2 ^ 149 := ht
        _ ≤ 10 ^ q * 2 ^ 149 := by nlinarith
        _ ≤ m * 10 ^ q * 2 ^ 149 := by
          have : (0 : ℝ) < 10 ^ q * 2 ^ 149 := by positivity
          nlinarith
  · rw [heb] at h2
    rw [F32Packing.pack_zero]
    have hlt : 2 * ((m : ℝ) * 10 ^ q * 2 ^ 149) < 1 := by
      set L := Nat.log2 m
      have hq : q ≤ -(257 + (L : ℤ)) := by omega
      have hmL : (m : ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_log2_self
      have h10 : (10 : ℝ) ^ q ≤ 10 ^ (-(257 + (L : ℤ))) := zpow_le_zpow_right₀ (by norm_num) hq
      have h2' : (10 : ℝ) ^ (-(257 + (L : ℤ))) ≤ 2 ^ (-(257 + (L : ℤ))) := by
        rw [zpow_neg, zpow_neg]
        apply inv_anti₀ (by positivity)
        rw [show (257 + (L : ℤ)) = ((257 + L : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
          zpow_natCast]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have hprod : (2 : ℝ) ^ (L + 1) * 2 ^ (-(257 + (L : ℤ))) * 2 ^ 149 = 2 ^ (-107 : ℤ) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num),
          ← zpow_add₀ (by norm_num)]
        congr 1; push_cast; ring
      have hsmall : (2 : ℝ) ^ (-107 : ℤ) < 1 / 2 := by
        rw [zpow_neg]; norm_num
      have : (m : ℝ) * 10 ^ q * 2 ^ 149 < 1 / 2 := by
        calc (m : ℝ) * 10 ^ q * 2 ^ 149 ≤ 2 ^ (L + 1) * 10 ^ q * 2 ^ 149 := by
              gcongr
          _ ≤ 2 ^ (L + 1) * 2 ^ (-(257 + (L : ℤ))) * 2 ^ 149 := by
              gcongr; exact h10.trans h2'
          _ = 2 ^ (-107 : ℤ) := hprod
          _ < 1 / 2 := hsmall
      linarith
    rw [refPos_small b32 _ (by positivity) hlt]
    rfl
  · have hm0 : 0 < m := Nat.pos_of_ne_zero h0
    rw [pack_mul_finite32]
    · rw [dyadic32 _ _ (by rw [hmb, Nat.shiftLeft_eq]; positivity)]
      have hq0 : (q.toNat : ℤ) = q := Int.toNat_of_nonneg h3
      have hx : (-((24 : ℕ) : ℤ) + 0 + 149).toNat = 125 := by decide
      rw [hmb, Nat.shiftLeft_eq, hx]
      have key : ((m * 2 ^ 24 * 10 ^ q.toNat * 2 ^ 125 : ℕ) : ℝ) / (2 : ℝ) ^ 0 =
          (m : ℝ) * (10 : ℝ) ^ q * 2 ^ 149 := by
        rw [← hq0, zpow_natCast, Int.toNat_natCast, pow_zero, div_one]
        push_cast
        rw [show (2 : ℝ) ^ 149 = 2 ^ 24 * 2 ^ 125 by rw [← pow_add]]
        ring
      rw [key]
    · rw [hmb]; norm_num
    · rw [hmb]
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
      have hM0 : m <<< 24 * 10 ^ q.toNat ≠ 0 := by rw [Nat.shiftLeft_eq]; positivity
      have hlog : 24 ≤ Nat.log2 (m <<< 24 * 10 ^ q.toNat) := by
        rw [Nat.le_log2 hM0, Nat.shiftLeft_eq]
        calc 2 ^ 24 = 1 * 2 ^ 24 * 1 := by ring
          _ ≤ m * 2 ^ 24 * 10 ^ q.toNat :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ hm0) (Nat.one_le_pow _ _ (by norm_num))
      have : (24 : ℤ) ≤ (Nat.log2 (m <<< 24 * 10 ^ q.toNat) : ℤ) := by exact_mod_cast hlog
      norm_num
      omega
  · have hm0 : 0 < m := Nat.pos_of_ne_zero h0
    rw [F32DivCore.pack_div_finite]
    · rw [show FloatCommon.negative (UnpackedFloat.Sign.positive / UnpackedFloat.Sign.positive) =
          false from rfl, rational32 _ _ (by positivity) (by positivity)]
      have hq0 : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      have hx : ((0 : ℤ) + 149).toNat = 149 := by decide
      rw [hx]
      have key : ((m * 2 ^ 149 * 2 ^ 149 : ℕ) : ℝ) / ((10 ^ (-q).toNat * 2 ^ 149 : ℕ) : ℝ) =
          (m : ℝ) * (10 : ℝ) ^ q * 2 ^ 149 := by
        have e1 : (10 : ℝ) ^ q = ((10 : ℝ) ^ (-q).toNat)⁻¹ := by
          rw [← zpow_natCast, hq0, zpow_neg, inv_inv]
        rw [e1]
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        have h2 : (2 : ℝ) ^ 149 ≠ 0 := by positivity
        have h10 : (10 : ℝ) ^ (-q).toNat ≠ 0 := by positivity
        field_simp
      rw [key]
    · norm_num
    · norm_num

/-- Lean's `Float32.ofScientific`, the meaning of a decimal literal of type `Float32`, is the
binary32 word of roundTiesToEven applied to `m · 10 ^ (±e)`. -/
theorem ofScientific32_spec (m : ℕ) (s : Bool) (e : ℕ) :
    (Float32.ofScientific m s e).toBits = round32 (.dec false m (if s then -(e : ℤ) else e)) := by
  rw [round32_pos]
  unfold Float32.ofScientific
  split
  · rename_i h
    cases s
    · simp only [Bool.false_eq_true, ite_false]
      exact fast_mul32 m e h.1 h.2 _
    · simp only [ite_true]
      exact fast_div32 m e h.1 h.2 _
  · cases s
    · simp only [Bool.false_eq_true, ite_false]
      exact slow_path32 m e
    · simp only [ite_true, Int.negOfNat_eq]
      exact slow_path32 m (-(e : ℤ))

#print axioms exact_word
#print axioms power_word32
#print axioms fast_div32
#print axioms fast_mul32
#print axioms slow_path32
#print axioms ofScientific32_spec

end Library.Numerics.Decimal.Shared.StrconvOfScientific32
