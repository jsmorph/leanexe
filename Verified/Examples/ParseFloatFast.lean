import Verified.Examples.ParseFloatDec
import Verified.Examples.StrconvOfScientific

/-!
Clinger's fast path of `ParseFloat.parse64`.  `Exact w A` says that a binary64 word is finite and
nonnegative with magnitude `A` units of `2 ^ -1074`.  For such words, Talos's `mul` and `div` are
the reference words of the product and the quotient (`mul_exact`, `div_exact`), by the argument of
`StrconvOfScientific.fast_mul` and `fast_div`.  `tenWord t` is the word that
`F64GridExact.signed_grid_packing_exact` gives for `5 ^ t` on the grid of `2 ^ (1074 + t)`, the
exact word of `10 ^ t` for `t ≤ 22`, and it is the reference word of `10 ^ t` (`tenWord_ref`).  So
`pow10Float k`, `k` multiplications by `10.0` starting from `1.0`, is exact (`pow10_exact`), and
`fastPath` is the reference word of `D · 10 ^ q` for `D < 2 ^ 53` and `|q| ≤ 22`
(`fastPath_spec`).
-/

namespace Verified.Examples.ParseFloatFast
open ParseFloat Uscale UscaleTheorem StrconvGrid StrconvWords StrconvRational StrconvOfScientific
  LeanExe.ProofKit ParseFloatRound

set_option exponentiation.threshold 4096

/-- A finite nonnegative binary64 word of magnitude `A` units of `2 ^ -1074`. -/
def Exact (w : UInt64) (A : ℕ) : Prop :=
  Wasm.IEEE64.isNaN w = false ∧ Wasm.IEEE64.isInfinite w = false ∧ Wasm.IEEE64.sign w = false ∧
    Wasm.IEEE64.scaledMagnitude w = A * 2 ^ 1074

/-- Talos's product of two exact words is the reference word of the product. -/
theorem mul_exact (a b : UInt64) (A B : ℕ) (ha : Exact a A) (hb : Exact b B) (hB : 0 < B) :
    Wasm.IEEE64.mul a b = UInt64.ofNat (refPos b64 ((A : ℝ) * B * 2 ^ 1074)) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have hP : (0 : ℕ) < 2 ^ 1074 := by positivity
  have hPr : ((2 ^ 1074 : ℕ) : ℝ) = (2 : ℝ) ^ 1074 := by push_cast; ring
  rw [← hPr]
  generalize hPd : 2 ^ 1074 = P at a4 b4 hP hPr ⊢
  have hb0 : (B * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
  rcases Nat.eq_zero_or_pos A with h0 | hpos
  · subst h0
    rw [refPos_small b64 _ (by simp) (by simp)]
    simp only [Wasm.IEEE64.mul, a1, a2, a3, a4, b1, b2, b3, b4, hb0, Bool.or_self,
      Bool.false_eq_true, ite_false, zero_mul, beq_self_eq_true, ite_true, Bool.true_or,
      bne_self_eq_false]
    rfl
  · have ha0 : (A * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
    simp only [Wasm.IEEE64.mul, a1, a2, a3, a4, b1, b2, b3, b4, hb0, ha0, Bool.or_self,
      Bool.false_eq_true, ite_false, bne_self_eq_false]
    rw [dyadic64 _ _ (by positivity)]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    have key : ((A * P * (B * P) : ℕ) : ℝ) / (2 : ℝ) ^ 1074 = (A : ℝ) * B * P := by
      rw [← hPr]; push_cast; field_simp
    rw [key]

/-- Talos's quotient of two exact words is the reference word of the quotient. -/
theorem div_exact (a b : UInt64) (A B : ℕ) (ha : Exact a A) (hb : Exact b B) (hB : 0 < B) :
    Wasm.IEEE64.div a b = UInt64.ofNat (refPos b64 ((A : ℝ) * (B : ℝ)⁻¹ * 2 ^ 1074)) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  have hP : (0 : ℕ) < 2 ^ 1074 := by positivity
  have hPr : ((2 ^ 1074 : ℕ) : ℝ) = (2 : ℝ) ^ 1074 := by push_cast; ring
  rw [← hPr]
  generalize hPd : 2 ^ 1074 = P at a4 b4 hP hPr ⊢
  have hb0 : (B * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
  rcases Nat.eq_zero_or_pos A with h0 | hpos
  · subst h0
    rw [refPos_small b64 _ (by simp) (by simp)]
    simp only [Wasm.IEEE64.div, a1, a2, a3, a4, b1, b2, b3, b4, hb0, Bool.or_self,
      Bool.false_eq_true, ite_false, zero_mul, beq_self_eq_true, ite_true, bne_self_eq_false]
    rfl
  · have ha0 : (A * P == 0) = false := by simp only [beq_eq_false_iff_ne]; positivity
    simp only [Wasm.IEEE64.div, a1, a2, a3, a4, b1, b2, b3, b4, hb0, ha0, Bool.or_self,
      Bool.false_eq_true, ite_false, bne_self_eq_false]
    rw [hPd, rational64 _ _ (by positivity) (by positivity)]
    have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    have key : ((A * P * P : ℕ) : ℝ) / ((B * P : ℕ) : ℝ) = (A : ℝ) * (B : ℝ)⁻¹ * P := by
      push_cast; field_simp
    rw [key]

/-! ### Powers of ten -/

/-- The word of `10 ^ t` on the grid of `2 ^ (1074 + t)`. -/
def tenWord (t : ℕ) : UInt64 := Wasm.IEEE64.roundScaledMagnitude false (5 ^ t * 2 ^ (1074 + t))

theorem five_pow (t : ℕ) (ht : t ≤ 22) : 5 ^ t < 2 ^ 53 :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) ht) (by norm_num)

theorem tenWord_exact (t : ℕ) (ht : t ≤ 22) : Exact (tenWord t) (10 ^ t) := by
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact ((5 ^ t : ℕ) : ℤ) (1074 + t)
    (by simp only [Int.natAbs_natCast]; exact (five_pow t ht).le) (by omega)
  have hc : Wasm.IEEE64.roundScaledMagnitude (decide (((5 ^ t : ℕ) : ℤ) < 0))
      ((((5 ^ t : ℕ) : ℤ)).natAbs * 2 ^ (1074 + t)) = tenWord t := by
    unfold tenWord
    rw [Int.natAbs_natCast, decide_eq_false (not_lt.mpr (by positivity))]
  rw [hc] at hf hv
  have hs : Wasm.IEEE64.sign (tenWord t) = false := by
    by_contra hs
    simp only [Bool.not_eq_false] at hs
    simp only [Wasm.IEEE64.scaledValue, hs, ite_true] at hv
    have h1 : (0 : ℤ) < ((5 ^ t : ℕ) : ℤ) * 2 ^ (1074 + t) := by positivity
    have h2 : (0 : ℤ) ≤ (Wasm.IEEE64.scaledMagnitude (tenWord t) : ℤ) := by positivity
    linarith
  refine ⟨CodeLib.IEEE64.not_nan_of_finite hf, CodeLib.IEEE64.not_infinite_of_finite hf, hs, ?_⟩
  simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false] at hv
  have hv' : Wasm.IEEE64.scaledMagnitude (tenWord t) = 5 ^ t * 2 ^ (1074 + t) := by
    exact_mod_cast hv
  rw [hv', pow_add, show (10 : ℕ) = 5 * 2 from rfl, mul_pow]
  ring

/-- `tenWord t` is the reference word of `10 ^ t`. -/
theorem tenWord_ref (t : ℕ) (ht : t ≤ 22) :
    tenWord t = UInt64.ofNat (refPos b64 ((10 : ℝ) ^ t * 2 ^ 1074)) := by
  set n := 5 ^ t * 2 ^ (1074 + t) with hn
  have h5 := five_pow t ht
  have h50 : 5 ^ t ≠ 0 := by positivity
  have hn0 : 0 < n := by positivity
  have hlog : Nat.log2 n = Nat.log2 (5 ^ t) + (1074 + t) := F64DyadicBounds.log2_mul_two_pow _ _ h50
  have hl5 : Nat.log2 (5 ^ t) < 53 := (Nat.log2_lt h50).mpr h5
  have hdy : Wasm.IEEE64.roundDyadicMagnitude false n 0 = Wasm.IEEE64.roundScaledMagnitude false n := by
    have hb : (n == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    unfold Wasm.IEEE64.roundDyadicMagnitude
    simp only [hb, Bool.false_eq_true, ite_false, zero_add, beq_self_eq_true, ite_true]
    by_cases hs : Nat.log2 n - 52 = 0
    · simp [hs]
    · have hs' : (Nat.log2 n - 52 == 0) = false := by simpa using hs
      simp only [hs', Bool.false_eq_true, ite_false]
      generalize hS : Nat.log2 n - 52 = S at hs ⊢
      have hS1 : S ≤ 1074 + t := by omega
      have hsplit : n = (5 ^ t * 2 ^ (1074 + t - S)) * 2 ^ S := by
        rw [hn, mul_assoc, ← pow_add, Nat.sub_add_cancel hS1]
      rw [hsplit, F64RoundFinish.roundShift_mul_pow _ _ (by omega)]
  unfold tenWord
  rw [← hn, ← hdy, dyadic64 _ _ hn0, pow_zero, div_one, hn]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add, show (10 : ℝ) = 5 * 2 by norm_num, mul_pow]
  refine congrArg (fun y => UInt64.ofNat (refPos b64 y)) ?_
  ring

theorem ref_exact (t : ℕ) (ht : t ≤ 22) :
    Exact (UInt64.ofNat (refPos b64 ((10 : ℝ) ^ t * 2 ^ 1074))) (10 ^ t) := by
  rw [← tenWord_ref t ht]; exact tenWord_exact t ht

theorem one_exact : Exact (1.0 : Float).toBits (10 ^ 0) := by
  have h : (1.0 : Float).toBits = UInt64.ofNat (refPos b64 ((10 : ℝ) ^ 0 * 2 ^ 1074)) := by
    show (Float.ofScientific 10 true 1).toBits = _
    rw [ofScientific_spec, round64_pos]
    exact congrArg (fun y => UInt64.ofNat (refPos b64 (y * 2 ^ 1074))) (by norm_num)
  rw [h]; exact ref_exact 0 (by norm_num)

theorem ten_exact : Exact (10.0 : Float).toBits (10 ^ 1) := by
  have h : (10.0 : Float).toBits = UInt64.ofNat (refPos b64 ((10 : ℝ) ^ 1 * 2 ^ 1074)) := by
    show (Float.ofScientific 100 true 1).toBits = _
    rw [ofScientific_spec, round64_pos]
    exact congrArg (fun y => UInt64.ofNat (refPos b64 (y * 2 ^ 1074))) (by norm_num)
  rw [h]; exact ref_exact 1 (by norm_num)

/-- `pow10Float k` is the exact word of `10 ^ k` for `k ≤ 22`. -/
theorem pow10_exact (k : ℕ) (hk : k ≤ 22) : Exact (pow10Float (UInt64.ofNat k)).toBits (10 ^ k) := by
  unfold pow10Float
  have hloop := loop_inv (UInt64.ofNat k) (1.0 : Float) (fun _ x => x * 10.0)
    (fun t x => t ≤ 22 → Exact x.toBits (10 ^ t)) (fun _ => one_exact)
    (by
      intro t x _ hP ht
      rw [F64Bits.toBits_mul, mul_exact _ _ _ _ (hP (by omega)) ten_exact (by norm_num)]
      have e : ((10 ^ t : ℕ) : ℝ) * ((10 ^ 1 : ℕ) : ℝ) * 2 ^ 1074 =
          (10 : ℝ) ^ (t + 1) * 2 ^ 1074 := by
        push_cast; ring
      rw [e]
      exact ref_exact (t + 1) ht)
  rw [ofNat_toNat _ (by omega)] at hloop
  exact hloop hk

/-! ### The fast path -/

/-- The first two limbs of a value below `2 ^ 64` as one word. -/
theorem two_limbs (D : Array UInt64) (hD : Limbs D) (hs : D.size < 2 ^ 32) (hv : val D < 2 ^ 64) :
    (limb D 0 ||| (limb D 1 <<< 32)) = (val D).toUInt64 := by
  have h0 := getElem!_digit D hD 0
  have h1 := getElem!_digit D hD 1
  rw [limb_eq D 0 (by omega), limb_eq D 1 (by omega)]
  simp only [UInt64.toNat_zero, UInt64.toNat_one, Nat.mul_zero, pow_zero, Nat.div_one,
    Nat.mul_one] at h0 h1 ⊢
  apply UInt64.toNat_inj.mp
  have hhi : (val D / 2 ^ 32 % 2 ^ 32) * 2 ^ 32 < 2 ^ 64 := by
    have := Nat.mod_lt (val D / 2 ^ 32) (show 0 < 2 ^ 32 by positivity)
    calc (val D / 2 ^ 32 % 2 ^ 32) * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_pos_right this (by positivity)
      _ = 2 ^ 64 := by norm_num
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, h0, h1, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhi, Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt (val D) (by positivity)),
    Nat.shiftLeft_eq, Nat.toUInt64_eq, ofNat_toNat _ hv]
  omega

/-- Clinger's fast path is the reference word of `D · 10 ^ q` for `D < 2 ^ 53` and `|q| ≤ 22`. -/
theorem fastPath_spec (D : Array UInt64) (hD : Limbs D) (hs : D.size < 2 ^ 32)
    (hv : val D < 2 ^ 53) (qb : UInt64) (h1 : 2 ^ 62 - 22 ≤ qb.toNat)
    (h2 : qb.toNat ≤ 2 ^ 62 + 22) :
    fastPath D qb =
      UInt64.ofNat (refPos b64 ((val D : ℝ) * (10 : ℝ) ^ ((qb.toNat : ℤ) - 2 ^ 62) * 2 ^ 1074)) := by
  unfold fastPath
  rw [two_limbs D hD hs (by omega)]
  obtain ⟨a1, a2, a3, a4⟩ := int_word (val D) hv
  have ha : Exact (Wasm.IEEE64.convertI64U (val D).toUInt64) (val D) := ⟨a1, a2, a3, a4⟩
  by_cases hq : qb ≥ 0x4000000000000000
  · rw [ite_eq_left hq]
    have hge : 2 ^ 62 ≤ qb.toNat := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, bias_toNat] at hq; exact hq
    have hk : qb - 0x4000000000000000 = UInt64.ofNat (qb.toNat - 2 ^ 62) := by
      apply UInt64.toNat_inj.mp
      rw [toNat_sub' _ _ (by rw [bias_toNat]; exact hge), bias_toNat, ofNat_toNat _ (by omega)]
    rw [hk, F64Bits.toBits_mul, F64Convert.toBits_toFloat,
      mul_exact _ _ _ _ ha (pow10_exact _ (by omega)) (by positivity)]
    have e : (qb.toNat : ℤ) - 2 ^ 62 = ((qb.toNat - 2 ^ 62 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  · rw [ite_eq_right hq]
    have hlt : qb.toNat < 2 ^ 62 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, bias_toNat] at hq; omega
    have hk : 0x4000000000000000 - qb = UInt64.ofNat (2 ^ 62 - qb.toNat) := by
      apply UInt64.toNat_inj.mp
      rw [toNat_sub' _ _ (by rw [bias_toNat]; omega), bias_toNat, ofNat_toNat _ (by omega)]
    rw [hk, F64Bits.toBits_div, F64Convert.toBits_toFloat,
      div_exact _ _ _ _ ha (pow10_exact _ (by omega)) (by positivity)]
    have e : (qb.toNat : ℤ) - 2 ^ 62 = -((2 ^ 62 - qb.toNat : ℕ) : ℤ) := by omega
    rw [e, zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]

#print axioms mul_exact
#print axioms div_exact
#print axioms tenWord_ref
#print axioms pow10_exact
#print axioms fastPath_spec

end Verified.Examples.ParseFloatFast
