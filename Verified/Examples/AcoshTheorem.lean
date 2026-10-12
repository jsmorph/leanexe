import Verified.Examples.AcoshTheoremSmallCases
import Verified.Examples.AcoshTheoremMid
import Verified.Examples.AsinhTheorem

/-!
**`acosh` within two steps** and its exceptional inputs.  For `x ≥ 1` the code takes
`log x + ln 2` from `2 ^ 28` (`AsinhTheoremLarge.acosh_large`), `+0` at 1,
`log (2x - 1/(x + √(x² - 1)))` from `2 (1 + 2 ^ -20)` (`AcoshTheoremMid.acosh_mid`), and
`log1p (t + √(2t + t²))` with `t = x - 1` below (`AcoshTheoremSmallCases.acosh_small`).  Its tests
read the high word `hx` and the low word of `x`.  For a word below `2 ^ 63` they are comparisons
of the word, which `F64PositiveOrder.value_le_iff` turns into comparisons of values.  `x < 1`,
`-0` included, `-∞`, and NaN give the canonical NaN, `+∞` gives `+∞`, and 1 gives `+0`.
-/

namespace Verified.Examples.AcoshTheorem
open CodeLib.IEEE64 LeanExe.ProofKit AsinhTheoremBranches

set_option exponentiation.threshold 4096

theorem hx_nat (x : Float) : (hxOf x).toNat = x.toBits.toNat / 2 ^ 32 := by
  unfold hxOf
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow]

theorem hx31_nat (x : Float) : (hxOf x >>> 31).toNat = x.toBits.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight, hx_nat, show (31 : UInt64).toNat % 64 = 31 from rfl,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]

/-- The first test of the code fails exactly for a word from 1 to below `2 ^ 63`. -/
theorem cond1 (x : Float) :
    (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false ↔
      0x3FF0000000000000 ≤ x.toBits.toNat ∧ x.toBits.toNat < 2 ^ 63 := by
  have hN := x.toBits.toNat_lt
  have h1 := hx_nat x
  have h2 := hx31_nat x
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not,
    ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, h1, h2, UInt64.reduceToNat]
  omega

/-- The test for `x = 1`, for a word at or above that of 1. -/
theorem one_test (x : Float) (h : 0x3FF0000000000000 ≤ x.toBits.toNat) :
    (((hxOf x - 0x3ff00000) ||| (x.toBits &&& 0xFFFFFFFF)) == 0) = true ↔
      x.toBits.toNat = 0x3FF0000000000000 := by
  have hN := x.toBits.toNat_lt
  have hge : (0x3ff00000 : UInt64) ≤ hxOf x := by
    rw [UInt64.le_iff_toNat_le, hx_nat]
    simp only [UInt64.reduceToNat]
    omega
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_or, UInt64.toNat_sub_of_le _ _ hge, hx_nat,
    Log1pTheoremReduce.low_nat, UInt64.toNat_zero, Nat.or_eq_zero_iff]
  simp only [UInt64.reduceToNat]
  omega

theorem zero_within_two : F64SignedRounding.WithinSteps 2 0 0 := by
  have h0 : F64PositiveRounding.roundNearestEven 0 = 0 := F64SignedRounding.positive_reference_zero
  exact F64SignedRounding.within_of_nonneg 2 0 le_rfl 0 (by decide) (by rw [h0]; decide)
    (by rw [h0]; decide)

theorem acosh_nan_eq (x : Float) (h : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = true) :
    Asinh.acosh x = (x - x) / (x - x) := by
  unfold hxOf at h
  simp only [Asinh.acosh, Asinh.acoshWith, h, ite_true]

theorem acosh_inf_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false)
    (h2 : hxOf x ≥ 0x41b00000) (h3 : hxOf x ≥ 0x7ff00000) : Asinh.acosh x = x + x := by
  unfold hxOf at h1 h2 h3
  simp only [Asinh.acosh, Asinh.acoshWith, h1, h2, h3, Bool.false_eq_true, ite_false, ite_true]

theorem acosh_one (x : Float) (h : x.toBits = 0x3FF0000000000000) :
    (Asinh.acosh x).toBits = 0 := by
  rw [acosh_one_eq x (by unfold hxOf; rw [h]; decide) (by unfold hxOf; rw [h]; decide)
    (by unfold hxOf; rw [h]; decide)]
  rfl

/-- **`acosh` within two steps.**  For every finite `x ≥ 1`, `Asinh.acosh x` lies within two
representable steps of the nearest-even rounding of `arcosh x`. -/
theorem acosh_within_two (x : Float) (hx : Finite x.toBits) (h1 : 1 ≤ value x.toBits) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits)) (Asinh.acosh x).toBits := by
  have hpos : x.toBits.toNat < 2 ^ 63 := by
    have := F64Exact.sign_of_pos x.toBits (by linarith)
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using this
  have hhx := hx_nat x
  have hfin := F64UpperWord.finite_high x.toBits hx
  rw [F64UpperWord.high_toNat] at hfin
  have hge1 : 0x3FF0000000000000 ≤ x.toBits.toNat := by
    have h := (F64PositiveOrder.value_le_iff (left := 0x3FF0000000000000) (by decide) hpos).mp (by
      rw [Log1pTheorem.word_value (0x3FF0000000000000 : UInt64) 1 (by decide +kernel)]
      push_cast
      exact h1)
    simpa only [UInt64.reduceToNat] using h
  have hc1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false := (cond1 x).mpr ⟨hge1, hpos⟩
  by_cases c2 : hxOf x ≥ 0x41b00000
  · have c2' := c2
    rw [ge_iff_le, UInt64.le_iff_toNat_le, hhx] at c2'
    simp only [UInt64.reduceToNat] at c2'
    have h3 : ¬ hxOf x ≥ 0x7ff00000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hhx]
      simp only [UInt64.reduceToNat]
      omega
    rw [acosh_log2_eq x hc1 c2 h3]
    have h := (F64PositiveOrder.value_le_iff (left := 0x41B0000000000000) (by decide) hpos).mpr
      (by simp only [UInt64.reduceToNat]; omega)
    rw [Log1pTheorem.word_value (0x41B0000000000000 : UInt64) (2 ^ 28) (by decide +kernel)] at h
    push_cast at h
    exact AsinhTheoremLarge.acosh_large x hx h
  by_cases c3 : x.toBits.toNat = 0x3FF0000000000000
  · have hb : x.toBits = 0x3FF0000000000000 :=
      UInt64.toNat_inj.mp (by simpa only [UInt64.reduceToNat] using c3)
    have hv : value x.toBits = 1 := by
      rw [hb, Log1pTheorem.word_value (0x3FF0000000000000 : UInt64) 1 (by decide +kernel)]
      norm_num
    rw [acosh_one x hb, hv, Real.arcosh_zero]
    exact zero_within_two
  have hc3 : (((hxOf x - 0x3ff00000) ||| (x.toBits &&& 0xFFFFFFFF)) == 0) = false :=
    Bool.eq_false_iff.mpr (fun h => c3 ((one_test x hge1).mp h))
  have hgt1 : 1 < value x.toBits := by
    have h := F64PositiveOrder.value_strict (left := 0x3FF0000000000000) hpos
      (by simp only [UInt64.reduceToNat]; omega)
    rw [Log1pTheorem.word_value (0x3FF0000000000000 : UInt64) 1 (by decide +kernel)] at h
    push_cast at h
    exact h
  have c2' := c2
  rw [ge_iff_le, UInt64.le_iff_toNat_le, hhx] at c2'
  simp only [UInt64.reduceToNat] at c2'
  by_cases c4 : hxOf x > 0x40000000
  · rw [acosh_mid_eq x hc1 c2 hc3 c4]
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hhx] at c4
    simp only [UInt64.reduceToNat] at c4
    have hlo := (F64PositiveOrder.value_le_iff (left := 0x4000000100000000) (by decide) hpos).mpr
      (by simp only [UInt64.reduceToNat]; omega)
    have hhi := (F64PositiveOrder.value_le_iff (right := 0x41B0000000000000) hpos (by decide)).mpr
      (by simp only [UInt64.reduceToNat]; omega)
    rw [Log1pTheorem.word_value (0x4000000100000000 : UInt64) (1048577 / 524288)
      (by decide +kernel)] at hlo
    rw [Log1pTheorem.word_value (0x41B0000000000000 : UInt64) (2 ^ 28) (by decide +kernel)] at hhi
    push_cast at hlo hhi
    exact AcoshTheoremMid.acosh_mid x hx
      (by linarith [(by norm_num : (2 : ℝ) ≤ 1048577 / 524288)]) hhi
  · rw [acosh_small_eq x hc1 c2 hc3 c4]
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hhx] at c4
    simp only [UInt64.reduceToNat] at c4
    have hhi := F64PositiveOrder.value_strict (left := x.toBits) (right := 0x4000000100000000)
      (by decide) (by simp only [UInt64.reduceToNat]; omega)
    rw [Log1pTheorem.word_value (0x4000000100000000 : UInt64) (1048577 / 524288)
      (by decide +kernel)] at hhi
    push_cast at hhi
    exact AcoshTheoremSmallCases.acosh_small x hx hgt1 hhi

/-- `x < 1`, `-0` included, `-∞`, and NaN give the canonical NaN. -/
theorem acosh_nan (x : Float)
    (h : Wasm.IEEE64.isNaN x.toBits = true ∨ x.toBits.toNat < 0x3FF0000000000000 ∨
      2 ^ 63 ≤ x.toBits.toNat) :
    (Asinh.acosh x).toBits = Wasm.IEEE64.canonicalNaN := by
  cases hc : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000)
  · obtain ⟨hge, hpos⟩ := (cond1 x).mp hc
    have hn : Wasm.IEEE64.isNaN x.toBits = true := by
      rcases h with h | h | h
      · exact h
      · omega
      · omega
    have hn' := hn
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at hn'
    have hhx := hx_nat x
    have h2 : hxOf x ≥ 0x41b00000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hhx]
      simp only [UInt64.reduceToNat]
      omega
    have h3 : hxOf x ≥ 0x7ff00000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hhx]
      simp only [UInt64.reduceToNat]
      omega
    rw [acosh_inf_eq x hc h2 h3, F64Bits.toBits_add]
    simp only [Wasm.IEEE64.add, hn, Bool.true_or, ite_true]
  · rw [acosh_nan_eq x hc, F64Bits.toBits_div, F64Bits.toBits_sub]
    exact AsinTheoremSpecial.self_quot_nan x.toBits

theorem acosh_inf (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Asinh.acosh x).toBits = 0x7FF0000000000000 := by
  rw [acosh_inf_eq x (by unfold hxOf; rw [h]; decide) (by unfold hxOf; rw [h]; decide)
    (by unfold hxOf; rw [h]; decide), F64Bits.toBits_add, h]
  exact AsinhTheorem.inf_add_self _ (by decide) (by decide)

#print axioms acosh_within_two
#print axioms acosh_nan
#print axioms acosh_inf
#print axioms acosh_one

end Verified.Examples.AcoshTheorem
