import Verified.Examples.Log10Main
import LeanExe.ProofKit.BorrowedKept
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
The accuracy theorem for `Log10.log10`.  For every finite binary64 input with positive value, the
result lies within one representable step of the nearest-even rounding of
`Real.logb 10 x = log x / log 10`, by `Log10Main.main10` for normal arguments and for subnormal
ones scaled by `2 ^ 54`.  The exceptional inputs give the results of IEEE 754:
`log10 (±0) = -∞`, `log10 (+∞) = +∞`, `log10 1 = +0`, and the canonical NaN for a negative
argument, negative infinity included, and for a NaN.  `log10 (10 ^ n) = n` for `n` from 0 to 22,
the exact powers of ten.  `log10_bytes_accuracy` carries the bound to the decoded bytes of the
compiled module and to every call in a sequence of calls to its export `log10`.
-/

namespace Verified.Examples.Log10Theorem
open CodeLib.IEEE64 LeanExe.ProofKit Log10Bits

set_option exponentiation.threshold 4096

/-- The words that `Log10.log10` tests, in terms of the argument word. -/
theorem guard_words (w : UInt64) :
    (w >>> 32).toNat = w.toNat / 4294967296 ∧
      (w >>> 32 >>> 31).toNat = w.toNat / 9223372036854775808 ∧
      (w >>> 32 &&& (0x7fffffff : UInt64)).toNat = w.toNat / 4294967296 % 2147483648 ∧
      (w &&& (0xFFFFFFFF : UInt64)).toNat = w.toNat % 4294967296 := by
  have h1 : (w >>> 32).toNat = w.toNat / 4294967296 := by
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
      Nat.reducePow]
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [UInt64.toNat_shiftRight, h1]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  · rw [UInt64.toNat_and, h1, show (0x7fffffff : UInt64).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
  · rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem neg_guard (w : UInt64) :
    (w >>> 32 >>> 31 == 1) = decide (9223372036854775808 ≤ w.toNat) := by
  have hw := w.toNat_lt
  obtain ⟨-, h2, -, -⟩ := guard_words w
  by_cases h : 9223372036854775808 ≤ w.toNat
  · rw [decide_eq_true h, beq_iff_eq, ← UInt64.toNat_inj, h2]
    simp only [UInt64.reduceToNat, Nat.reducePow] at hw ⊢
    omega
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    have := congrArg UInt64.toNat h'
    rw [h2] at this
    simp only [UInt64.reduceToNat] at this
    omega

theorem zero_guard (w : UInt64) :
    ((w >>> 32 &&& (0x7fffffff : UInt64)) ||| (w &&& (0xFFFFFFFF : UInt64)) == 0) =
      decide (w.toNat % 9223372036854775808 = 0) := by
  have hw := w.toNat_lt
  obtain ⟨-, -, h3, h4⟩ := guard_words w
  have hor : ((w >>> 32 &&& (0x7fffffff : UInt64)) ||| (w &&& (0xFFFFFFFF : UInt64))).toNat =
      w.toNat / 4294967296 % 2147483648 ||| w.toNat % 4294967296 := by
    rw [UInt64.toNat_or, h3, h4]
  by_cases h : w.toNat % 9223372036854775808 = 0
  · rw [decide_eq_true h, beq_iff_eq, ← UInt64.toNat_inj, hor, Nat.or_eq_zero_iff.mpr ⟨by omega, by omega⟩]
    rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    have := congrArg UInt64.toNat h'
    rw [hor] at this
    simp only [UInt64.reduceToNat] at this
    obtain ⟨a, b⟩ := Nat.or_eq_zero_iff.mp this
    omega

theorem lt_guard (w : UInt64) (c : Nat) (hc : c < 4294967296) :
    (w >>> 32 < UInt64.ofNat c) ↔ w.toNat / 4294967296 < c := by
  obtain ⟨h1, -, -, -⟩ := guard_words w
  rw [UInt64.lt_iff_toNat_lt, h1, UInt64.toNat_ofNat_of_lt' (lt_trans hc (by decide))]

theorem eq_guard (w : UInt64) (c : Nat) (hc : c < 4294967296) :
    (w >>> 32 == UInt64.ofNat c) = decide (w.toNat / 4294967296 = c) := by
  obtain ⟨h1, -, -, -⟩ := guard_words w
  by_cases h : w.toNat / 4294967296 = c
  · rw [decide_eq_true h, beq_iff_eq, ← UInt64.toNat_inj, h1, UInt64.toNat_ofNat_of_lt' (lt_trans hc (by decide)), h]
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h'
    have := congrArg UInt64.toNat h'
    rw [h1, UInt64.toNat_ofNat_of_lt' (lt_trans hc (by decide))] at this
    exact h this

/-- `Log10.log10` on a positive normal argument other than 1. -/
theorem log10_normal_within (x : Float) (hf : Finite x.toBits)
    (hs : Wasm.IEEE64.sign x.toBits = false) (he : 1 ≤ Wasm.IEEE64.exponent x.toBits)
    (hne : x.toBits ≠ 0x3FF0000000000000) :
    F64SignedRounding.WithinSteps 1 (Real.logb 10 (value x.toBits)) (Log10.log10 x).toBits := by
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    exact hf
  have hN : x.toBits.toNat = Wasm.IEEE64.exponent x.toBits * 4503599627370496 +
      Wasm.IEEE64.fraction x.toBits := by
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow] at he hfin ⊢
    simp only [Nat.reducePow] at hlt
    omega
  have hF : Wasm.IEEE64.fraction x.toBits < 4503599627370496 := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hE2 : Wasm.IEEE64.exponent x.toBits ≤ 2046 := by
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hne' : x.toBits.toNat ≠ 4607182418800017408 := by
    intro h
    exact hne (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = false := by
    rw [neg_guard, decide_eq_false_iff_not]
    simp only [Nat.reducePow] at hlt
    omega
  have hlo : ¬ x.toBits >>> 32 < 0x00100000 := by
    rw [show (0x00100000 : UInt64) = UInt64.ofNat 1048576 from rfl, lt_guard _ _ (by norm_num)]
    omega
  have hinf : ¬ x.toBits >>> 32 ≥ 0x7ff00000 := by
    rw [ge_iff_le, show (0x7ff00000 : UInt64) = UInt64.ofNat 2146435072 from rfl, UInt64.not_le,
      lt_guard _ _ (by norm_num)]
    omega
  have hone : (x.toBits >>> 32 == 0x3ff00000 && x.toBits &&& (0xFFFFFFFF : UInt64) == 0) = false := by
    rw [show (0x3ff00000 : UInt64) = UInt64.ofNat 1072693248 from rfl, eq_guard _ _ (by norm_num),
      Bool.and_eq_false_iff]
    by_cases h : x.toBits.toNat / 4294967296 = 1072693248
    · right
      rw [beq_eq_false_iff_ne]
      intro h'
      have := congrArg UInt64.toNat h'
      rw [(guard_words x.toBits).2.2.2] at this
      simp only [UInt64.reduceToNat] at this
      omega
    · left
      exact decide_eq_false h
  obtain ⟨hxr, hhi, hw⟩ := Log10Main.main10 x.toBits 0 (Wasm.IEEE64.exponent x.toBits)
    (Wasm.IEEE64.fraction x.toBits) 0 he hE2 hF hN (by simp) (by norm_num)
    (fun h hF0 => hne' (by omega))
  rw [Log10Bits.normal_bits x hneg hlo hinf hone hxr hhi, Real.logb, LogMain.normal_form _ hs he]
  simpa using hw

/-- `Log10.log10` on a positive subnormal argument, which the code scales by `2 ^ 54`. -/
theorem log10_subnormal_within (x : Float) (hlo : 0 < x.toBits.toNat)
    (hhi : x.toBits.toNat < 4503599627370496) :
    F64SignedRounding.WithinSteps 1 (Real.logb 10 (value x.toBits)) (Log10.log10 x).toBits := by
  have hxe : Wasm.IEEE64.exponent x.toBits = 0 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hxfr : Wasm.IEEE64.fraction x.toBits = x.toBits.toNat := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hxf : Finite x.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hxe]
    decide
  have hxs : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    omega
  have hxm : Wasm.IEEE64.scaledMagnitude x.toBits = x.toBits.toNat * 2 ^ 0 := by
    simp only [Wasm.IEEE64.scaledMagnitude, hxe, hxfr, beq_self_eq_true, ↓reduceIte]
    ring
  have hcf : Finite (0x4350000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  have hcm : Wasm.IEEE64.scaledMagnitude (0x4350000000000000 : UInt64) = 1 * 2 ^ 1128 := by
    decide +kernel
  have hcs : Wasm.IEEE64.sign (0x4350000000000000 : UInt64) = false := by decide
  have hcv : value (0x4350000000000000 : UInt64) = 2 ^ 54 := by
    have h : PolyBound.ratOfWord 0x4350000000000000 = 2 ^ 54 := by decide +kernel
    rw [← PolyBound.ratOfWord_cast, h]
    norm_num
  obtain ⟨hwf, hwv, hwm, hws⟩ := F64ExactProduct.mul_exact_scaled x.toBits _ hxf hcf
    x.toBits.toNat 1 0 1128 hxm hcm (by omega) (by norm_num) (by norm_num)
  rw [hxs, hcs, hcv] at *
  simp only [bne_self_eq_false] at hws
  set w := Wasm.IEEE64.mul x.toBits 0x4350000000000000 with hwdef
  obtain ⟨e, he⟩ : ∃ e, Wasm.IEEE64.exponent w = e := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, Wasm.IEEE64.fraction w = f := ⟨_, rfl⟩
  have hflt : f < 4503599627370496 := by
    rw [← hf]
    simp only [Wasm.IEEE64.fraction]
    omega
  have hwlt : w.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hws
    exact hws
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    have hsm : Wasm.IEEE64.scaledMagnitude w = f := by
      simp only [Wasm.IEEE64.scaledMagnitude, he, hf, he0, beq_self_eq_true, ↓reduceIte]
    rw [hsm] at hwm
    have : 4503599627370496 ≤ x.toBits.toNat * 1 * 2 ^ (0 + 1128 - 1074) := by
      simp only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, mul_one]
      omega
    omega
  have hsm : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + f) * 2 ^ (e - 1) := by
    have hne : (e == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf, hne, Bool.false_eq_true, ↓reduceIte]
  have he54 : e ≤ 54 := by
    rw [hsm] at hwm
    simp only [Nat.reduceAdd, Nat.reduceSub, mul_one] at hwm
    have h1 : 2 ^ 52 * 2 ^ (e - 1) ≤ (2 ^ 52 + f) * 2 ^ (e - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : x.toBits.toNat * 2 ^ 54 < 2 ^ 52 * 2 ^ 54 :=
      Nat.mul_lt_mul_of_pos_right (by simp only [Nat.reducePow]; omega) (by positivity)
    have h3 : 2 ^ (e - 1) < 2 ^ 54 := by
      have : 2 ^ 52 * 2 ^ (e - 1) < 2 ^ 52 * 2 ^ 54 := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  have hwN : w.toNat = e * 4503599627370496 + f := by
    rw [← he, ← hf]
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow]
    simp only [Nat.reducePow] at hwlt
    omega
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = false := by
    rw [neg_guard, decide_eq_false_iff_not]
    omega
  have hlo' : x.toBits >>> 32 < 0x00100000 := by
    rw [show (0x00100000 : UInt64) = UInt64.ofNat 1048576 from rfl, lt_guard _ _ (by norm_num)]
    omega
  have hz : ((x.toBits >>> 32 &&& (0x7fffffff : UInt64)) ||| (x.toBits &&& (0xFFFFFFFF : UInt64))
      == 0) = false := by
    rw [zero_guard, decide_eq_false_iff_not]
    omega
  have hinf : ¬ w >>> 32 ≥ 0x7ff00000 := by
    rw [ge_iff_le, show (0x7ff00000 : UInt64) = UInt64.ofNat 2146435072 from rfl, UInt64.not_le,
      lt_guard _ _ (by norm_num)]
    omega
  have hone : (w >>> 32 == 0x3ff00000 && x.toBits &&& (0xFFFFFFFF : UInt64) == 0) = false := by
    rw [show (0x3ff00000 : UInt64) = UInt64.ofNat 1072693248 from rfl, eq_guard _ _ (by norm_num),
      Bool.and_eq_false_iff]
    left
    rw [decide_eq_false_iff_not]
    omega
  obtain ⟨hxr, hhi', hwithin⟩ := Log10Main.main10 w (0 - 54) e f (-54) he1 (by omega) hflt hwN
    (by decide) (by norm_num) (by omega)
  rw [Log10Bits.subnormal_bits x hneg hlo' hz hinf hone hxr hhi', Real.logb]
  have hxv : value x.toBits = ((2 : ℝ) ^ 52 + f) * (2 : ℝ) ^ ((e : Int) - 1075) * (2 : ℝ) ^ (-54 : Int) := by
    have hwv' := LogMain.normal_form w hws (by rw [he]; exact he1)
    rw [he, hf] at hwv'
    rw [← hwv', hwv, mul_assoc, ← zpow_natCast (2 : ℝ) 54, ← zpow_add₀ (by norm_num)]
    norm_num
  rw [hxv]
  exact hwithin

theorem log10_one_bits (x : Float) (h : x.toBits = 0x3FF0000000000000) :
    (Log10.log10 x).toBits = 0 := by
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = false := by rw [h]; decide
  have hlo : ¬ x.toBits >>> 32 < 0x00100000 := by rw [h]; decide
  have hinf : ¬ x.toBits >>> 32 ≥ 0x7ff00000 := by rw [h]; decide
  have hone : (x.toBits >>> 32 == 0x3ff00000 && x.toBits &&& (0xFFFFFFFF : UInt64) == 0) = true := by
    rw [h]; decide
  simp only [Log10.log10, hneg, hlo, hinf, hone, decide_false, Bool.false_or, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, ite_true]
  rfl

/-- `log10 (±0) = -∞`. -/
theorem log10_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Log10.log10 x).toBits = 0xFFF0000000000000 := by
  have hc : ((x.toBits >>> 32 >>> 31 == 1 || x.toBits >>> 32 < 0x00100000) &&
      ((x.toBits >>> 32 &&& (0x7fffffff : UInt64)) ||| (x.toBits &&& (0xFFFFFFFF : UInt64))) == 0)
      = true := by
    rcases h with h | h <;> rw [h] <;> decide
  simp only [Log10.log10, hc, ↓reduceIte, eq_self_iff_true, ite_true]
  rw [F64Bits.toBits_div, F64Bits.toBits_neg]
  decide +kernel

/-- `log10 (+∞) = +∞`. -/
theorem log10_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Log10.log10 x).toBits = 0x7FF0000000000000 := by
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = false := by rw [h]; decide
  have hlo : ¬ x.toBits >>> 32 < 0x00100000 := by rw [h]; decide
  have hinf : x.toBits >>> 32 ≥ 0x7ff00000 := by rw [h]; decide
  simp only [Log10.log10, hneg, hlo, hinf, decide_false, Bool.false_or, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  rw [F64Bits.toBits_add, h]
  decide

/-- A negative argument other than `-0`, negative infinity included, gives the canonical NaN. -/
theorem log10_negative (x : Float) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hz : x.toBits ≠ 0x8000000000000000) :
    (Log10.log10 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hge : 9223372036854775808 ≤ x.toBits.toNat := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
    simpa using hs
  have hne : x.toBits.toNat ≠ 9223372036854775808 := by
    intro h
    exact hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hlt := x.toBits.toNat_lt
  simp only [Nat.reducePow] at hlt
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = true := by
    rw [neg_guard, decide_eq_true_eq]
    exact hge
  have hzz : ((x.toBits >>> 32 &&& (0x7fffffff : UInt64)) ||| (x.toBits &&& (0xFFFFFFFF : UInt64))
      == 0) = false := by
    rw [zero_guard, decide_eq_false_iff_not]
    omega
  simp only [Log10.log10, hneg, hzz, Bool.true_or, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
    eq_self_iff_true, ite_true]
  apply invalid10_bits
  by_cases he : Wasm.IEEE64.exponent x.toBits = 2047
  · by_cases hfr : Wasm.IEEE64.fraction x.toBits = 0
    · right; right
      apply UInt64.toNat_inj.mp
      simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at he hfr
      simp only [UInt64.reduceToNat]
      omega
    · left
      simp only [Wasm.IEEE64.isNaN, he, hfr, beq_self_eq_true, bne_iff_ne, ne_eq, not_false_eq_true,
        Bool.and_self, decide_true]
      simpa using hfr
  · right; left
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    exact he

/-- A NaN gives the canonical NaN. -/
theorem log10_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Log10.log10 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hlt := x.toBits.toNat_lt
  have hnan : Wasm.IEEE64.exponent x.toBits = 2047 ∧ Wasm.IEEE64.fraction x.toBits ≠ 0 := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact ⟨h.1, h.2⟩
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at hnan
  simp only [Nat.reducePow] at hlt
  by_cases hs : 9223372036854775808 ≤ x.toBits.toNat
  · have hneg : (x.toBits >>> 32 >>> 31 == 1) = true := by
      rw [neg_guard, decide_eq_true_eq]
      exact hs
    have hzz : ((x.toBits >>> 32 &&& (0x7fffffff : UInt64)) |||
        (x.toBits &&& (0xFFFFFFFF : UInt64)) == 0) = false := by
      rw [zero_guard, decide_eq_false_iff_not]
      omega
    simp only [Log10.log10, hneg, hzz, Bool.true_or, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte, eq_self_iff_true, ite_true]
    exact invalid10_bits x (Or.inl h)
  · have hneg : (x.toBits >>> 32 >>> 31 == 1) = false := by
      rw [neg_guard, decide_eq_false_iff_not]
      exact hs
    have hlo : ¬ x.toBits >>> 32 < 0x00100000 := by
      rw [show (0x00100000 : UInt64) = UInt64.ofNat 1048576 from rfl, lt_guard _ _ (by norm_num)]
      omega
    have hinf : x.toBits >>> 32 ≥ 0x7ff00000 := by
      rw [ge_iff_le, show (0x7ff00000 : UInt64) = UInt64.ofNat 2146435072 from rfl, ← UInt64.not_lt,
        lt_guard _ _ (by norm_num)]
      omega
    simp only [Log10.log10, hneg, hlo, hinf, decide_false, Bool.false_or, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    rw [F64Bits.toBits_add]
    simp only [Wasm.IEEE64.add, h, Bool.true_or, ↓reduceIte]

/-- `Log10.log10` on every finite argument with positive value, against `Real.logb 10`. -/
theorem log10_within_one (x : Float) (hf : Finite x.toBits) (hpos : 0 < value x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.logb 10 (value x.toBits)) (Log10.log10 x).toBits := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      have : value x.toBits = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h]
        split <;> simp
      linarith
    · exact h
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    cases h : Wasm.IEEE64.sign x.toBits
    · rfl
    · exact absurd ((F64Magnitude.sign_value _ hmag).mp h) (not_lt.mpr hpos.le)
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hnz : 0 < x.toBits.toNat := by
    rcases Nat.eq_zero_or_pos x.toBits.toNat with h | h
    · exfalso
      have h0 : Wasm.IEEE64.scaledMagnitude x.toBits = 0 := by
        simp [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, h]
      omega
    · exact h
  by_cases hsub : x.toBits.toNat < 4503599627370496
  · exact log10_subnormal_within x hnz hsub
  · have he : 1 ≤ Wasm.IEEE64.exponent x.toBits := by
      simp only [Wasm.IEEE64.exponent]
      simp only [Nat.reducePow] at hlt
      omega
    by_cases hone : x.toBits = 0x3FF0000000000000
    · have hv1 : value x.toBits = 1 := by
        rw [hone]
        exact (Log10Main.one_word).2
      have hb : (Log10.log10 x).toBits = 0 := log10_one_bits x hone
      rw [hv1, Real.logb_one, hb]
      exact F64SignedRounding.within_of_nonneg 1 0 le_rfl 0 (by decide)
        (by rw [F64SignedRounding.positive_reference_zero]; decide)
        (by rw [F64SignedRounding.positive_reference_zero]; decide)
    · exact log10_normal_within x hf hs he hone

/-- The words of `10 ^ n` for `n` from 0 to 22, the powers of ten that binary64 holds exactly. -/
def pow10Words : List UInt64 :=
  [0x3FF0000000000000, 0x4024000000000000, 0x4059000000000000, 0x408F400000000000,
    0x40C3880000000000, 0x40F86A0000000000, 0x412E848000000000, 0x416312D000000000,
    0x4197D78400000000, 0x41CDCD6500000000, 0x4202A05F20000000, 0x42374876E8000000,
    0x426D1A94A2000000, 0x42A2309CE5400000, 0x42D6BCC41E900000, 0x430C6BF526340000,
    0x4341C37937E08000, 0x4376345785D8A000, 0x43ABC16D674EC800, 0x43E158E460913D00,
    0x4415AF1D78B58C40, 0x444B1AE4D6E2EF50, 0x4480F0CF064DD592]

/-- The words of the integers from 0 to 22. -/
def pow10Logs : List UInt64 :=
  [0x0, 0x3FF0000000000000, 0x4000000000000000, 0x4008000000000000, 0x4010000000000000,
    0x4014000000000000, 0x4018000000000000, 0x401C000000000000, 0x4020000000000000,
    0x4022000000000000, 0x4024000000000000, 0x4026000000000000, 0x4028000000000000,
    0x402A000000000000, 0x402C000000000000, 0x402E000000000000, 0x4030000000000000,
    0x4031000000000000, 0x4032000000000000, 0x4033000000000000, 0x4034000000000000,
    0x4035000000000000, 0x4036000000000000]

/-- The kernel's evaluation of `Log10Bits.tailWord` at each power of ten, with the facts that
`Log10Bits.normal_bits` needs. -/
theorem pow10_checks : ∀ i : Fin 23,
    PolyBound.ratOfWord (pow10Words.getD i.val 0) = 10 ^ i.val ∧
    PolyBound.ratOfWord (pow10Logs.getD i.val 0) = i.val ∧
    (pow10Words.getD i.val 0).toNat < 2 ^ 63 ∧
    (i.val ≠ 0 →
      ((pow10Words.getD i.val 0) >>> 32 >>> 31 == 1) = false ∧
      ¬ (pow10Words.getD i.val 0) >>> 32 < 0x00100000 ∧
      ¬ (pow10Words.getD i.val 0) >>> 32 ≥ 0x7ff00000 ∧
      ((pow10Words.getD i.val 0) >>> 32 == 0x3ff00000 &&
        (pow10Words.getD i.val 0) &&& (0xFFFFFFFF : UInt64) == 0) = false ∧
      Wasm.IEEE64.isNaN (xrOf (pow10Words.getD i.val 0)) = false ∧
      Wasm.IEEE64.isNaN (Wasm.IEEE64.sub
        (Wasm.IEEE64.sub (xrOf (pow10Words.getD i.val 0)) 0x3FF0000000000000)
        (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000
          (Wasm.IEEE64.sub (xrOf (pow10Words.getD i.val 0)) 0x3FF0000000000000))
          (Wasm.IEEE64.sub (xrOf (pow10Words.getD i.val 0)) 0x3FF0000000000000)) &&&
        (0xFFFFFFFF00000000 : UInt64)) = false ∧
      tailWord (Wasm.IEEE64.sub (xrOf (pow10Words.getD i.val 0)) 0x3FF0000000000000)
        (Log2Power.kdBits (kWord10 (pow10Words.getD i.val 0) 0)) = pow10Logs.getD i.val 0) := by
  decide +kernel

/-- `log10 (10 ^ n) = n` for `n` from 0 to 22. -/
theorem log10_pow10 (x : Float) (n : Nat) (hn : n ≤ 22) (hx : value x.toBits = 10 ^ n) :
    value (Log10.log10 x).toBits = n := by
  obtain ⟨hw, hr, hw63, hrest⟩ := pow10_checks ⟨n, by omega⟩
  simp only at hw hr hw63 hrest
  have hwv : value (pow10Words.getD n 0) = 10 ^ n := by
    rw [← PolyBound.ratOfWord_cast, hw]
    push_cast
    rfl
  have hpos : 0 < value x.toBits := by rw [hx]; positivity
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      have : value x.toBits = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h]
        split <;> simp
      linarith
    · exact h
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    cases h : Wasm.IEEE64.sign x.toBits
    · rfl
    · exact absurd ((F64Magnitude.sign_value _ hmag).mp h) (not_lt.mpr hpos.le)
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hxw : x.toBits = pow10Words.getD n 0 := by
    apply UInt64.toNat_inj.mp
    rcases lt_trichotomy x.toBits.toNat (pow10Words.getD n 0).toNat with h | h | h
    · have := F64PositiveOrder.value_strict (left := x.toBits) (right := pow10Words.getD n 0) hw63 h
      linarith
    · exact h
    · have := F64PositiveOrder.value_strict (left := pow10Words.getD n 0) (right := x.toBits) hlt h
      linarith
  have hrv : value (pow10Logs.getD n 0) = n := by
    rw [← PolyBound.ratOfWord_cast, hr]
    push_cast
    rfl
  by_cases h0 : n = 0
  · subst h0
    have h1 : x.toBits = 0x3FF0000000000000 := by rw [hxw]; rfl
    rw [log10_one_bits x h1, F64Magnitude.value_zero]
    simp
  · obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hrest h0
    rw [← hxw] at c1 c2 c3 c4 c5 c6 c7
    rw [Log10Bits.normal_bits x c1 c2 c3 c4 c5 c6, c7, hrv]

open Wasm LeanExe.Pipeline in
/-- A store from which the module's `log10` entry runs, with `heap` the allocator's state: the
allocator invariant holds and the memory cap is at most 65,535 pages.  The module has no tables. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap Log10.compiled.module 0 ≤ 65535

open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap Log10.compiled.tables) Log10.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, -⟩ := Log10.compiled.initial
  exact ⟨hAt, hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `log10` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Log10.log10 x` and leaves a ready store, and every region of
the heap before the call keeps its bytes and stays a region. -/
theorem log10_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Log10.compiled.module 3 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Log10.log10 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  refine (Log10.compiled.log10.implements env store heap [.f64 x.toBits] x hAt trivial rfl
    Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Log10.log10 x).toBits] := howned
  have hvs : values = [.f64 (Log10.log10 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 3 of the module is its export `log10`. -/
theorem log10_export :
    ({ name := "log10", funcIdx := 3 } : Wasm.Export) ∈ Log10.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module: its bytes decode to the module, whose function 3
is exported as `log10`, and the store in which the module starts is ready.  A call of that entry
from a ready store returns without a trap a single `f64` whose bits are those of
`Log10.log10 x`, and it leaves a ready store in which every region of the heap before the call
keeps its bytes.  The theorem therefore covers every call in a sequence of calls to `log10` from
the initial store.  For finite `x` with positive value the bits lie within one representable step
of the nearest-even rounding of `Real.logb 10 x`. -/
theorem log10_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Log10.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Log10.compiled.module ∧
      ({ name := "log10", funcIdx := 3 } : Wasm.Export) ∈ Log10.compiled.module.exports ∧
      Ready (Verified.initialHeap Log10.compiled.tables) Log10.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Log10.compiled.module 3 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Log10.log10 x).toBits ∧
            (Finite x.toBits → 0 < value x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.logb 10 (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log10.compiled.bytes
  refine ⟨bytes, henc, hdec, log10_export, ready_initial,
    fun env heap store x h => (log10_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Log10.log10 x).toBits, hv, rfl, log10_within_one x, hrest⟩

#print axioms guard_words
#print axioms log10_normal_within
#print axioms log10_subnormal_within
#print axioms log10_one_bits
#print axioms log10_zero
#print axioms log10_pos_infinity
#print axioms log10_negative
#print axioms log10_nan
#print axioms log10_within_one
#print axioms pow10_checks
#print axioms log10_pow10
#print axioms ready_initial
#print axioms log10_entry_call
#print axioms log10_export
#print axioms log10_bytes_accuracy

end Verified.Examples.Log10Theorem
