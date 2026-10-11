import Verified.Examples.Exp2Branches
import LeanExe.ProofKit.F64RelativeStep

/-!
The accuracy theorem for `Exp2.exp2`.  For every finite binary64 input `a`, the result lies
within one representable step of the nearest-even rounding of the real `2 ^ a`, overflow to
positive infinity and underflow to zero included.  The exceptional inputs give `exp2 (±0) = 1`,
`exp2 (+∞) = +∞`, `exp2 (-∞) = +0`, and the canonical NaN for a NaN.
-/

namespace Verified.Examples.Exp2Theorem
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude ExpBranches F64ExponentBounds

set_option exponentiation.threshold 4096

/-- `1 + x` for `|x| ≤ 2 ^ -54`. -/
theorem tiny_within (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1 / 2 ^ 54) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x) (ExpTinyError.result x) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have h2 : (2 : ℝ) ^ value x = Real.exp (value x * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h2]
  have hone := ExpTinyError.one_value
  have honef : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hxb := abs_le.mp hx
  have hsum : |value 0x3FF0000000000000 + value x| < (2 : ℝ) ^ 1023 := by
    rw [hone, abs_lt]
    constructor <;> linarith [show (1 : ℝ) / 2 ^ 54 ≤ 1 by norm_num,
      show (2 : ℝ) < 2 ^ 1023 by norm_num]
  obtain ⟨hrf, hre⟩ := F64AddBounds.add_real_relative _ x honef hxf hsum
  rw [hone] at hre
  have hL := ExpReductionBounds.log_two_coarse_bounds
  have hy : |value x * Real.log 2| ≤ 1 / 2 ^ 54 := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < Real.log 2 by linarith [hL.1])]
    calc
      _ ≤ 1 / 2 ^ 54 * 1 := mul_le_mul hx (by linarith [hL.2]) (by linarith [hL.1])
        (by positivity)
      _ = _ := by ring
  have hb := Real.exp_bound (x := value x * Real.log 2) (hy.trans (by norm_num)) (n := 2)
    (by norm_num)
  have hs : ∑ i ∈ Finset.range 2, (value x * Real.log 2) ^ i / (i.factorial : ℝ) =
      1 + value x * Real.log 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one,
      Nat.cast_one, div_one, zero_add, Nat.succ_eq_add_one, Nat.cast_mul]
    ring
  rw [hs] at hb
  have hy2 : |value x * Real.log 2| ^ 2 ≤ (1 / 2 ^ 54) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hc : |value x * Real.log 2| ^ 2 *
      ((Nat.succ 2 : Nat) / ((Nat.factorial 2 : Nat) * (2 : Nat)) : ℝ) ≤ (1 / 2 ^ 54) ^ 2 * 1 :=
    mul_le_mul hy2 (by norm_num [Nat.factorial]) (by positivity) (by positivity)
  have hb' := abs_le.mp hb
  -- `|x - x log 2| ≤ |x| / 3`
  have hlin : |value x - value x * Real.log 2| ≤ 1 / 2 ^ 54 * (1 / 3) := by
    rw [show value x - value x * Real.log 2 = value x * (1 - Real.log 2) by ring, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - Real.log 2 by linarith [hL.2])]
    exact mul_le_mul hx (by linarith [hL.1]) (by linarith [hL.2]) (by positivity)
  have hlin' := abs_le.mp hlin
  have hr' := abs_le.mp hre
  have hpos : 1 - 1 / 2 ^ 54 ≤ Real.exp (value x * Real.log 2) := by
    have := Real.add_one_le_exp (value x * Real.log 2)
    have := (abs_le.mp hy).1
    linarith
  have h1x : |1 + value x| ≤ 1 + 1 / 2 ^ 54 := by
    rw [abs_le]
    constructor <;> linarith [show (1 : ℝ) / 2 ^ 54 ≤ 1 by norm_num]
  have hre' : |value (Wasm.IEEE64.add 0x3FF0000000000000 x) - (1 + value x)| ≤
      1 / 2 ^ 53 * (1 + 1 / 2 ^ 54) := by
    rw [hu] at hre
    exact hre.trans (mul_le_mul_of_nonneg_left h1x (by positivity))
  have hre'' := abs_le.mp hre'
  apply F64RelativeStep.within_one_relative _ _ hrf
  · rw [abs_of_pos (Real.exp_pos _)]
    have : (1 : ℝ) / 2 ^ 1000 ≤ 1 - 1 / 2 ^ 54 := by norm_num
    linarith
  · rw [abs_of_pos (Real.exp_pos _), hu]
    have hnum : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 54) + 1 / 2 ^ 54 * (1 / 3) +
        (1 / 2 ^ 54) ^ 2 * 1 ≤ 11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) := by norm_num
    have hmono : 11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) ≤
        11 / 8 * (1 / 2 ^ 53) * Real.exp (value x * Real.log 2) :=
      mul_le_mul_of_nonneg_left hpos (by positivity)
    rw [abs_le]
    constructor <;> linarith

/-- The positive reference of a number at least `2 ^ 1024` is positive infinity. -/
theorem overflow_within (E : ℝ) (hE : (2 : ℝ) ^ 1024 ≤ E) :
    F64SignedRounding.WithinSteps 1 E 0x7FF0000000000000 := by
  have ht : F64PositiveRounding.overflowThreshold ≤ E := by
    have : F64PositiveRounding.overflowThreshold ≤ (2 : ℝ) ^ 1024 := by
      rw [F64PositiveRounding.overflowThreshold]
      norm_num
    exact this.trans hE
  have hr := F64PositiveRounding.reference_overflow E ht
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  refine F64SignedRounding.within_of_nonneg 1 E hE0 _ (by decide) ?_ ?_ <;>
    rw [hr] <;> decide

/-- Positive zero lies within one step of the reference of a positive number at most
`2 ^ -1075`. -/
theorem zero_within (E : ℝ) (hE : 0 < E) (hEt : E ≤ 1 / (2 : ℝ) ^ 1075) :
    F64SignedRounding.WithinSteps 1 E 0 := by
  have hbnd : value (UInt64.ofNat (2 * 2 ^ 52)) = (2 : ℝ) ^ (-1021 : Int) :=
    F64NearestBinade.boundary_power 2 (-1021) (by norm_num) (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) / 2 ^ 1075 ≤ (2 : ℝ) ^ (-1021 : Int) := by norm_num
  have h2 : (1 : ℝ) / 2 ^ 1075 < 3 * ((2 : ℝ) ^ (0 - 1) / (2 : ℝ) ^ 1074) / 2 := by norm_num
  have hs := F64FullStep.one_step_binades E 0 0 2 (by norm_num) (by norm_num)
    (by rw [value_zero_boundary]; exact hE.le) (fun _ => by rw [hbnd]; exact hEt.trans h1)
    (by decide) (by rw [value_zero_boundary, value_zero])
    (by rw [hbnd, value_zero]; positivity) (by
      rw [value_zero, zero_sub, abs_neg, abs_of_pos hE]
      linarith)
  exact F64SignedRounding.within_of_nonneg 1 E hE.le 0 (by decide) hs.1 hs.2

theorem neg_word_value (x : UInt64) (hxf : Finite x) (hs : Wasm.IEEE64.sign x = true) :
    (Wasm.IEEE64.negate x).toNat = x.toNat - 2 ^ 63 ∧
      value (Wasm.IEEE64.negate x) = -value x ∧ Finite (Wasm.IEEE64.negate x) := by
  have h := F64SignedRounding.negate_toNat x
  rw [hs] at h
  obtain ⟨hf, hv⟩ := negate_value x hxf
  exact ⟨by simpa using h, hv, hf⟩

theorem word_1075 : value (0x4090CC0000000000 : UInt64) = 1075 := by
  have h : Wasm.IEEE64.scaledValue (0x4090CC0000000000 : UInt64) = 1075 * (2 : Int) ^ 1074 := by
    decide +kernel
  rw [value, h, Int.cast_mul, Int.cast_pow]
  norm_num

/-- For a negative word, the bits at or above those of `-1075` mean a value at most `-1075`. -/
theorem underflow_bits (x : UInt64) (hxf : Finite x) (hs : Wasm.IEEE64.sign x = true) :
    (x ≥ 0xC090CC0000000000 ↔ value x ≤ -1075) := by
  obtain ⟨hn, hv, hf⟩ := neg_word_value x hxf hs
  have hsn : 2 ^ 63 ≤ x.toNat := by simpa [Wasm.IEEE64.sign] using hs
  have hx := x.toNat_lt
  have hl : (Wasm.IEEE64.negate x).toNat < 2 ^ 63 := by rw [hn]; omega
  have hw : (0x4090CC0000000000 : UInt64).toNat < 2 ^ 63 := by decide
  have hiff := F64PositiveOrder.value_le_iff hw hl
  rw [word_1075, hv] at hiff
  rw [ge_iff_le, UInt64.le_iff_toNat_le]
  constructor
  · intro h
    have : (0x4090CC0000000000 : UInt64).toNat ≤ (Wasm.IEEE64.negate x).toNat := by
      rw [hn]
      change 0xC090CC0000000000 ≤ x.toNat at h
      change 0x4090CC0000000000 ≤ x.toNat - 2 ^ 63
      omega
    have := hiff.mpr this
    linarith
  · intro h
    have := hiff.mp (by linarith)
    rw [hn] at this
    change 0x4090CC0000000000 ≤ x.toNat - 2 ^ 63 at this
    change 0xC090CC0000000000 ≤ x.toNat
    omega

theorem sign_shift (x : UInt64) : (x >>> 63 == 0) = !Wasm.IEEE64.sign x := by
  have hlt := x.toNat_lt
  simp only [Wasm.IEEE64.sign]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true h]
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg UInt64.toNat heq
    rw [UInt64.toNat_shiftRight] at this
    change x.toNat >>> 63 = 0 at this
    rw [Nat.shiftRight_eq_div_pow] at this
    omega
  · rw [decide_eq_false h]
    apply beq_iff_eq.mpr
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight]
    change x.toNat >>> 63 = 0
    rw [Nat.shiftRight_eq_div_pow]
    omega

theorem two_rpow_ge (a b : ℝ) (h : b ≤ a) : (2 : ℝ) ^ b ≤ 2 ^ a :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem two_rpow_nat (n : Nat) : (2 : ℝ) ^ (n : ℝ) = 2 ^ n := Real.rpow_natCast 2 n

/-- The accuracy theorem: `Exp2.exp2` is within one step of the nearest-even rounding of
`2 ^ a` for every finite input `a`. -/
theorem exp2_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits) (Exp2.exp2 x).toBits := by
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  rw [Exp2.exp2]
  rcases (show Wasm.IEEE64.exponent x.toBits < 969 ∨
      (969 ≤ Wasm.IEEE64.exponent x.toBits ∧ Wasm.IEEE64.exponent x.toBits < 1032) ∨
      Wasm.IEEE64.exponent x.toBits = 1032 ∨ 1033 ≤ Wasm.IEEE64.exponent x.toBits by omega)
    with he | ⟨he1, he2⟩ | he | he
  · have hx : |value x.toBits| ≤ 1 / 2 ^ 54 := by
      have h := magnitude_le_boundary x.toBits 969 (by decide) he
      rwa [tiny_boundary, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 54)] at h
    rw [Exp2Branches.tiny_selected _ x he, ExpTinyError.float_result_bits]
    exact tiny_within _ hxf hx
  · have hx := magnitude_lt x.toBits 1032 9 (by norm_num) (by norm_num) he2
    rw [Exp2Branches.ordinary_selected _ x he1 he2]
    exact Exp2Paths.ordinary_within x hxf (by norm_num at hx; linarith)
  · have hlo := magnitude_ge x.toBits 1032 9 (by norm_num) (by norm_num) (by norm_num) he.ge
    have hhi := magnitude_lt x.toBits 1033 10 (by norm_num) (by norm_num) (by omega)
    norm_num at hlo hhi
    rw [Exp2Branches.special_selected _ x he, Exp2Branches.flag_special _ he]
    by_cases h928 : 928 < |value x.toBits|
    · rw [decide_eq_true h928]
      rcases le_or_gt 0 (value x.toBits) with hpos | hneg
      · rw [abs_of_nonneg hpos] at h928 hhi
        exact Exp2Paths.positive_within x hxf h928
          (Exp2Branches.below_top _ hhi)
      · rw [abs_of_neg hneg] at h928 hhi
        exact Exp2Paths.negative_within x hxf (by linarith) (by linarith)
    · rw [decide_eq_false h928]
      exact Exp2Paths.ordinary_within x hxf (le_of_not_gt h928)
  · have hge := magnitude_ge x.toBits 1033 10 (by norm_num) (by norm_num) (by norm_num) he
    norm_num at hge
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
      simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
        show Wasm.IEEE64.exponent x.toBits ≠ 0 by omega, ite_false]
      positivity
    by_cases hs : Wasm.IEEE64.sign x.toBits = true
    · have hs' : ¬ (x.toBits >>> 63 == 0) = true := by rw [sign_shift, hs]; decide
      have hneg := (sign_value _ hmag).mp hs
      rw [abs_of_neg hneg] at hge
      by_cases hb : x.toBits ≥ 0xC090CC0000000000
      · rw [Exp2Branches.underflow_selected _ x he hf hs' hb, ExpTheorem.underflow_product]
        have hv := (underflow_bits _ hxf hs).mp hb
        apply zero_within _ (Real.rpow_pos_of_pos (by norm_num) _)
        have hm := two_rpow_ge (-(1075 : Nat) : ℝ) (value x.toBits) (by push_cast; linarith)
        rw [Real.rpow_neg (by norm_num), two_rpow_nat, inv_eq_one_div] at hm
        exact hm
      · have hv : -1075 < value x.toBits := by
          by_contra hn
          exact hb ((underflow_bits _ hxf hs).mpr (le_of_not_gt hn))
        rw [Exp2Branches.big_core_selected _ x he hf hs' hb (Exp2Branches.flag_big _ he)]
        exact Exp2Paths.negative_within x hxf hv (by linarith)
    · have hs' : (x.toBits >>> 63 == 0) = true := by
        rw [sign_shift]
        simpa using hs
      have hpos : 0 < value x.toBits := by
        rcases lt_or_ge (value x.toBits) 0 with h | h
        · exact absurd ((sign_value _ hmag).mpr h) hs
        · rcases h.lt_or_eq with h | h
          · exact h
          · rw [← h] at hge
            norm_num at hge
      rw [abs_of_pos hpos] at hge
      rw [Exp2Branches.overflow_selected _ x he hf hs', ExpTheorem.overflow_product]
      apply overflow_within
      have hm := two_rpow_ge (value x.toBits) ((1024 : Nat) : ℝ) (by push_cast; linarith)
      rw [two_rpow_nat] at hm
      exact hm

theorem exp2_pos_infinity :
    (Exp2.exp2 (Float.ofBits 0x7FF0000000000000)).toBits = 0x7FF0000000000000 := by
  have hb : (Float.ofBits 0x7FF0000000000000).toBits = 0x7FF0000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp2, Exp2Branches.nonfinite_selected _ _ (by rw [hb]; decide +kernel)
    (by rw [hb]; decide), ExpTinyError.float_result_bits, hb]
  decide +kernel

theorem exp2_neg_infinity : (Exp2.exp2 (Float.ofBits 0xFFF0000000000000)).toBits = 0 := by
  have hb : (Float.ofBits 0xFFF0000000000000).toBits = 0xFFF0000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp2, Exp2Branches.neg_infinity_selected _ _ hb]
  rfl

theorem exp2_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Exp2.exp2 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hc := F64Bits.toBits_canonical x
  rw [ite_eq_left h] at hc
  rw [Exp2.exp2, Exp2Branches.nonfinite_selected _ _ (by rw [← hc]; decide +kernel)
    (by rw [← hc]; decide), ExpTinyError.float_result_bits, ← hc]
  decide +kernel

theorem exp2_pos_zero : (Exp2.exp2 (Float.ofBits 0)).toBits = 0x3FF0000000000000 := by
  have hb : (Float.ofBits 0).toBits = 0 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp2, Exp2Branches.tiny_selected _ _ (by rw [hb]; decide +kernel),
    ExpTinyError.float_result_bits, hb]
  decide +kernel

theorem exp2_neg_zero :
    (Exp2.exp2 (Float.ofBits 0x8000000000000000)).toBits = 0x3FF0000000000000 := by
  have hb : (Float.ofBits 0x8000000000000000).toBits = 0x8000000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp2, Exp2Branches.tiny_selected _ _ (by rw [hb]; decide +kernel),
    ExpTinyError.float_result_bits, hb]
  decide +kernel

#print axioms tiny_within
#print axioms overflow_within
#print axioms zero_within
#print axioms underflow_bits
#print axioms sign_shift
#print axioms exp2_within
#print axioms exp2_pos_infinity
#print axioms exp2_neg_infinity
#print axioms exp2_nan
#print axioms exp2_pos_zero
#print axioms exp2_neg_zero

end Verified.Examples.Exp2Theorem
