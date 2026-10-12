import Verified.Examples.BesselDivTop
import LeanExe.ProofKit.F64NegateOps
import LeanExe.ProofKit.F64NearestRelative
import Verified.Examples.BesselY1Small

/-!
`Bessel.y1 x` for positive `x` on the code's first path, below about `2^-54`, subnormal arguments
included: the result lies within one representable step of the nearest-even double to `Y₁(x)`
(`y1_tiny`), in the sense of `F64SignedRounding.WithinSteps 1`.  The code returns `-tpi/x`, the
negation of the rounded quotient `c = tpi/x` (`F64NegateOps.div_negate_left`).  The exact quotient
`s` lies within `0.36 u/x` of `2/(π x)`, and `-Y₁(x)` within `300 x` of it
(`BesselY1Small.tiny_close`), so `|s - (-Y₁(x))|` is far below one unit of roundoff relative to
either.  While both stay below the overflow threshold, `c` is a nearest word of `s`
(`F64NearestDiv.div_nearest` up to `2^1022`, `BesselDivTop.div_top` above) and
`F64NearestRelative.within_rel_k` gives one step.  When either reaches the threshold, both lie
above the midpoint below the largest finite double, and `c` and the reference are each that double
or positive infinity (`BesselDivTop.nearest_top`).
-/

namespace Verified.Examples.BesselY1Tiny
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64Approx BesselPQEval BesselCombine
  BesselSmallY0 BesselY0Small BesselY1Small BesselDivTop F64NearestNonnegative Real
open LeanExe.ProofKit.Bessel (Y1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 4096

def tpiWord : UInt64 := 0x3FE45F306DC9C883

theorem tpi_bits : Bessel.tpi.toBits = tpiWord := by
  unfold Bessel.tpi
  rw [F64Bits.toBits_ofBits, show Wasm.IEEE64.isNaN 0x3FE45F306DC9C883 = false by decide]
  simp only [Bool.false_eq_true, ite_false]
  rfl

theorem tpi_value : |value tpiWord - 2 / π| ≤ 36 / 100 * 𝐮 := by
  have h := tpi_near.2
  rw [tpi_bits] at h
  exact h

/-- The steps from the reference when both the word and the reference are the largest finite
double or positive infinity. -/
theorem within_top (y : ℝ) (hy : 0 ≤ y) (c : UInt64)
    (hc : c.toNat = 0x7FEFFFFFFFFFFFFF ∨ c.toNat = 0x7FF0000000000000)
    (hr : (F64PositiveRounding.roundNearestEven y).toNat = 0x7FEFFFFFFFFFFFFF ∨
      (F64PositiveRounding.roundNearestEven y).toNat = 0x7FF0000000000000) :
    F64SignedRounding.WithinSteps 1 y c :=
  F64SignedRounding.within_of_nonneg 1 y hy c (by omega) (by omega) (by omega)

/-- The reference of `y` above the midpoint below the largest finite double. -/
theorem reference_top (y : ℝ) (hy : 2 ^ 1024 - 3 * 2 ^ 970 < y) :
    (F64PositiveRounding.roundNearestEven y).toNat = 0x7FEFFFFFFFFFFFFF ∨
      (F64PositiveRounding.roundNearestEven y).toNat = 0x7FF0000000000000 := by
  by_cases ht : F64PositiveRounding.overflowThreshold ≤ y
  · right
    rw [F64PositiveRounding.reference_overflow y ht]
    rfl
  · left
    push Not at ht
    rw [F64PositiveRounding.reference_finite y ht]
    exact nearest_top y _ (F64NearestEven.roundNearestEven_spec y).1 hy ht.le

/-- `y1 x` for `0 < x` up to the high word `0x3c900000`. -/
theorem y1_tiny (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) (ht : x.toBits.toNat < 0x3C90000100000000) :
    F64SignedRounding.WithinSteps 1 (Y1 (value x.toBits)) (Bessel.y1 x).toBits := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hixN := TrigSinCos.high_word x.toBits
  have hN : x.toBits.toNat % 2 ^ 63 = x.toBits.toNat := Nat.mod_eq_of_lt hpos
  set v := value x.toBits with hvdef
  have hv0 : 0 < v := by
    have h := F64PositiveOrder.value_strict (left := (0 : UInt64)) (right := x.toBits) hpos
      (by simp only [UInt64.toNat_zero]; omega)
    rwa [F64Magnitude.value_zero] at h
  have hsmall : v < 1 / 2 ^ 53 := by
    have h := F64PositiveOrder.value_strict (left := x.toBits)
      (right := (0x3CA0000000000000 : UInt64)) (by decide) (by simp only [UInt64.reduceToNat]; omega)
    have e : value (0x3CA0000000000000 : UInt64) = 1 / 2 ^ 53 := by
      rw [← ratOfWord_cast]
      have : ratOfWord 0x3CA0000000000000 = 1 / 2 ^ 53 := by decide +kernel
      rw [this]; norm_num
    rwa [e] at h
  have hmin := value_ge_min x.toBits hpos hv0
  obtain ⟨hlabs, -, hl2⟩ := log_facts v hmin (by norm_num at hsmall ⊢; linarith)
  have hcl := tiny_close v hv0 hsmall.le (by rw [hlabs]; exact hl2)
  -- the code
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by
      rw [BesselSpecial.double_zero, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 63 == 1) = true by
      rw [BesselSpecial.sign_bit, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_left (show x.toBits >>> 32 &&& 2147483647 ≤ 1016070144 by
      rw [UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  have hTf : Finite tpiWord := by unfold tpiWord CodeLib.IEEE64.Finite; decide
  have hTs : Wasm.IEEE64.sign tpiWord = false := by decide
  have hXs : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]; omega
  have hX0 : Wasm.IEEE64.scaledMagnitude x.toBits ≠ 0 := by
    intro h0
    have : value x.toBits = 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    rw [← hvdef] at this
    linarith
  have hneg : (-Bessel.tpi).toBits = Wasm.IEEE64.negate tpiWord := by
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, tpi_bits, not_nan_of_finite hTf]
    simp only [Bool.false_eq_true, ite_false]
  rw [F64Bits.toBits_div, hneg, F64NegateOps.div_negate_left tpiWord x.toBits hTf hxf hX0]
  set c := Wasm.IEEE64.div tpiWord x.toBits with hcdef
  have hY : Y1 v = -(-Y1 v) := by ring
  rw [hY, F64SignedRounding.within_negate]
  -- the exact quotient `s` and `y = -Y₁(x)`
  set s := value tpiWord / v with hsdef
  set y := -Y1 v with hydef
  set Y := 1 / v with hYdef
  have hY53 : (2 : ℝ) ^ 53 ≤ Y := by
    rw [hYdef, le_div_iff₀ hv0]; norm_num at hsmall ⊢; linarith
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY53
  have htv := tpi_value
  obtain ⟨hp1, hp2⟩ := pi_bounds
  have hpi0 := Real.pi_pos
  have h2pi : 2 / π * Y = 2 / (π * v) := by rw [hYdef]; ring
  have h2lo : 6366 / 10000 ≤ 2 / π := by rw [le_div_iff₀ hpi0]; linarith
  have h2hi : 2 / π ≤ 6367 / 10000 := by rw [div_le_iff₀ hpi0]; linarith
  have hs_eq : s = value tpiWord * Y := by rw [hsdef, hYdef]; ring
  have hsd : |s - 2 / π * Y| ≤ 36 / 100 * 𝐮 * Y := by
    rw [hs_eq, ← sub_mul, abs_mul, abs_of_nonneg hY0]
    exact mul_le_mul_of_nonneg_right htv hY0
  have hyd : |y - 2 / π * Y| ≤ 300 * v := by
    rw [hydef, h2pi]
    rw [show -Y1 v - 2 / (π * v) = -(Y1 v - -(2 / (π * v))) by ring, abs_neg]
    exact hcl
  have hv300 : 300 * v ≤ 1 / 10 ^ 10 * 𝐮 * Y := by
    rw [hu]
    have : v ≤ 1 / 2 ^ 53 := hsmall.le
    have h1 : (1 : ℝ) / 10 ^ 10 * (1 / 2 ^ 53) * 2 ^ 53 ≤ 1 / 10 ^ 10 * (1 / 2 ^ 53) * Y :=
      mul_le_mul_of_nonneg_left hY53 (by positivity)
    norm_num at this h1 ⊢
    linarith
  have hsy : |s - y| ≤ 3601 / 10000 * 𝐮 * Y := by
    have := abs_sub_le s (2 / π * Y) y
    rw [abs_sub_comm (2 / π * Y) y] at this
    linarith
  have hsY : 6365 / 10000 * Y ≤ s := by
    have := (abs_le.mp hsd).1
    have h1 := mul_le_mul_of_nonneg_right h2lo hY0
    rw [hu] at this
    linarith
  have hyY : 6365 / 10000 * Y ≤ y := by
    have := (abs_le.mp hyd).1
    have h1 := hv300
    have h3 := mul_le_mul_of_nonneg_right h2lo hY0
    rw [hu] at h1
    linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hyY
  have hth := threshold_eq
  -- `c` as a nearest word of `s`, or positive infinity
  have hcases : (c.toNat = 0x7FF0000000000000 ∧ F64PositiveRounding.overflowThreshold ≤ s) ∨
      (Nearest s c ∧ s ≤ F64PositiveRounding.overflowThreshold) := by
    by_cases hs22 : s < 2 ^ 1022
    · right
      refine ⟨?_, by rw [hth]; norm_num at hs22 ⊢; linarith⟩
      have hs1 : (1 : ℝ) / 2 ^ 1022 ≤ s := by
        have : (1 : ℝ) / 2 ^ 1022 ≤ 6365 / 10000 * 2 ^ 53 := by norm_num
        linarith
      exact F64NearestDiv.div_nearest tpiWord x.toBits hTf hxf hTs hXs hs1 hs22
    · push Not at hs22
      rcases div_top tpiWord x.toBits hTf hxf hTs hXs hs22 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        refine ⟨?_, h2⟩
        show (Wasm.IEEE64.div tpiWord x.toBits).toNat = _
        rw [h1]
        rfl
      · right
        exact ⟨h1, h2⟩
  have hbig : ∀ a b : ℝ, |a - b| ≤ 3601 / 10000 * 𝐮 * Y → 6365 / 10000 * Y ≤ a →
      F64PositiveRounding.overflowThreshold ≤ a → 2 ^ 1024 - 3 * 2 ^ 970 < b := by
    intro a b hab ha1 ha2
    rw [hth] at ha2
    have := (abs_le.mp hab).2
    rw [hu] at this
    linarith
  rcases hcases with ⟨hc, hst⟩ | ⟨hc, hst⟩
  · exact within_top y hy0 c (Or.inr hc) (reference_top y (hbig s y hsy hsY hst))
  · by_cases hmax : max y s < F64PositiveRounding.overflowThreshold
    · refine F64NearestRelative.within_rel_k 1 le_rfl y s c ?_ hmax hc ?_
      · have : (1 : ℝ) / 2 ^ 1022 ≤ 6365 / 10000 * 2 ^ 53 := by norm_num
        rw [le_min_iff]
        constructor <;> linarith
      · simp only [Nat.cast_one, one_mul]
        have hm : 6365 / 10000 * Y ≤ min y s := le_min hyY hsY
        have h1 : (1 - 1 / 2 ^ 50) * 𝐮 * (6365 / 10000 * Y) ≤ (1 - 1 / 2 ^ 50) * 𝐮 * min y s :=
          mul_le_mul_of_nonneg_left hm (by rw [hu]; positivity)
        have h2 : 3601 / 10000 * 𝐮 * Y ≤ (1 - 1 / 2 ^ 50) * 𝐮 * (6365 / 10000 * Y) := by
          rw [hu]; linarith [hY0]
        linarith
    · push Not at hmax
      have hs_top : 2 ^ 1024 - 3 * 2 ^ 970 < s := by
        rcases le_max_iff.mp hmax with h | h
        · rw [abs_sub_comm] at hsy
          exact hbig y s hsy hyY h
        · rw [hth] at h; linarith [show (2 : ℝ) ^ 970 > 0 by positivity]
      have hy_top : 2 ^ 1024 - 3 * 2 ^ 970 < y := by
        rcases le_max_iff.mp hmax with h | h
        · rw [hth] at h; linarith [show (2 : ℝ) ^ 970 > 0 by positivity]
        · exact hbig s y hsy hsY h
      exact within_top y hy0 c (Or.inl (nearest_top s c hc hs_top hst)) (reference_top y hy_top)

#print axioms within_top
#print axioms reference_top
#print axioms y1_tiny

end Verified.Examples.BesselY1Tiny
