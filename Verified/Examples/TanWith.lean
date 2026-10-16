import Verified.Examples.TanOddStep
import Verified.Examples.TanBigStep
import Verified.Examples.TrigTheorem
import LeanExe.ProofKit.F64Convert

/-!
The accuracy of `Tan.tan` for every finite input: the result lies within one step of the
nearest-even rounding of `tan x`.  Below `2 ^ -27` the result is `x` itself, within `|x| ^ 3` of
`tan x`.  Up to the high word `0x3fe921fb` the kernel runs on `x` with no tail.  Above, the
kernel runs on the reduction of `|x|`, the quadrant count `N` turns `tan r` or `-1/tan r` into
`tan |x|`, and the result is negated for a negative `x`.
-/

namespace Verified.Examples.TanWith

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanOdd TanEven TanOddStep TanBigWords TanBigStep
  TanBigClose TrigSinCos TrigReduce

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 1200

/-- `Float.toUInt64` truncates a finite value below 1 in magnitude to 0. -/
theorem toUInt64_small (x : Float) (hxf : Finite x.toBits) (h : |value x.toBits| < 1) :
    x.toUInt64 = 0 := by
  rw [F64Convert.toUInt64_eq]
  have hm : Wasm.IEEE64.scaledMagnitude x.toBits < 2 ^ 1074 := by
    rw [F64RoundNearest.abs_value, div_lt_one (by positivity)] at h
    exact_mod_cast h
  have hfin : Wasm.IEEE64.isFinite x.toBits = true := hxf
  have hnan : Wasm.IEEE64.isNaN x.toBits = false := not_nan_of_finite hxf
  have htr : Wasm.IEEE64.truncatedInt x.toBits = some 0 := by
    have h0 : Wasm.IEEE64.scaledMagnitude x.toBits / 2 ^ 1074 = 0 := Nat.div_eq_of_lt hm
    unfold Wasm.IEEE64.truncatedInt
    simp only [hfin, ite_true, h0, Nat.cast_zero, neg_zero, ite_self]
  unfold Wasm.IEEE64.truncSatI64U
  simp only [hnan, Bool.false_eq_true, ite_false, htr, le_refl, ite_true]

/-- `|tan a - a| ≤ |a| ^ 3` near 0. -/
theorem tan_cube (a : ℝ) (ha : |a| ≤ 1 / 10) : |Real.tan a - a| ≤ |a| ^ 3 := by
  have hc := cos_small a (by linarith)
  have hs := Real.sin_bound (x := a) (by linarith)
  have hcb := Real.cos_bound (x := a) (by linarith)
  have hc0 : Real.cos a ≠ 0 := ne_of_gt (by linarith)
  have hid : Real.tan a - a = (Real.sin a - a * Real.cos a) / Real.cos a := by
    rw [Real.tan_eq_sin_div_cos, eq_div_iff hc0, sub_mul, div_mul_cancel₀ _ hc0]
  rw [hid, abs_div, abs_of_pos (by linarith : 0 < Real.cos a), div_le_iff₀ (by linarith)]
  have e1 : Real.sin a - a * Real.cos a = (Real.sin a - (a - a ^ 3 / 6)) -
      a * (Real.cos a - (1 - a ^ 2 / 2)) + a ^ 3 / 3 := by ring
  rw [e1]
  have t1 := abs_add_le ((Real.sin a - (a - a ^ 3 / 6)) - a * (Real.cos a - (1 - a ^ 2 / 2)))
    (a ^ 3 / 3)
  have t2 := sub_abs (Real.sin a - (a - a ^ 3 / 6)) (a * (Real.cos a - (1 - a ^ 2 / 2)))
  rw [abs_mul] at t2
  have t3 : |a| * |Real.cos a - (1 - a ^ 2 / 2)| ≤ |a| * (|a| ^ 4 * (5 / 96)) :=
    mul_le_mul_of_nonneg_left hcb (abs_nonneg a)
  have t4 : |a ^ 3 / 3| = |a| ^ 3 / 3 := by rw [abs_div, abs_pow]; norm_num
  have h2 : |a| ^ 2 ≤ 1 / 100 :=
    calc |a| ^ 2 ≤ (1 / 10) ^ 2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
      _ = 1 / 100 := by norm_num
  have h3 : 0 ≤ |a| ^ 3 := by positivity
  have p5 : |a| ^ 5 ≤ |a| ^ 3 * (1 / 100) := by
    rw [show |a| ^ 5 = |a| ^ 3 * |a| ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left h2 h3
  have p6 : |a| * (|a| ^ 4 * (5 / 96)) = |a| ^ 5 * (5 / 96) := by ring
  have p7 : |a| ^ 3 * (99 / 100) ≤ |a| ^ 3 * Real.cos a := mul_le_mul_of_nonneg_left hc h3
  linarith

/-- `x` is within one step of `tan x` below `2 ^ -27`. -/
theorem tiny_tan (x : UInt64) (hxf : Finite x) (hx : |value x| < 1 / 2 ^ 27)
    (hA : x.toNat % 2 ^ 63 = 0 ↔ value x = 0) :
    F64SignedRounding.WithinSteps 1 (Real.tan (value x)) x := by
  by_cases h0 : value x = 0
  · rw [h0, Real.tan_zero]
    exact F64SelfStep.zero_step x (hA.mpr h0)
  · refine F64SelfStep.self_step x _ hxf h0 (hx.le.trans (by norm_num)) ?_
    have hc := tan_cube (value x) (hx.le.trans (by norm_num))
    rw [abs_sub_comm]
    have h2 : |value x| ^ 2 ≤ 1 / 2 ^ 54 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hx.le 2
      rw [div_pow, one_pow, ← _root_.pow_mul] at this
      exact this
    have h3 : |value x| ^ 3 ≤ |value x| / 2 ^ 54 := by
      rw [show |value x| ^ 3 = |value x| * |value x| ^ 2 by ring,
        show |value x| / 2 ^ 54 = |value x| * (1 / 2 ^ 54) by ring]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith

theorem thresholds :
    value (0x3E40000000000000 : UInt64) = 1 / 2 ^ 27 ∧
      value (0x3FE5942800000000 : UInt64) = 1414184 / 2 ^ 21 := by
  refine ⟨?_, ?_⟩
  · rw [TrigReduce.value_word _ 1 27 (by norm_num) (by decide +kernel)]
    norm_num
  · rw [TrigReduce.value_word _ 1414184 21 (by norm_num) (by decide +kernel)]
    norm_num

theorem smallW_even (x y : UInt64) : smallW x y false = Wasm.IEEE64.add x (corrW x y) := by
  simp only [smallW, Bool.not_false, ↓reduceIte]

theorem zero_toBits : (0.0 : Float).toBits = 0 := by decide

/-- The kernel on `x + y` near `r`, for `|x|` from `2 ^ -70` to `0.78541`. -/
theorem kernel_within (y0 y1 : Float) (odd : Bool) (r X : ℝ) (f0 : Finite y0.toBits)
    (f1 : Finite y1.toBits) (hX : |value y0.toBits| = X) (hX0 : 1 / 2 ^ 70 ≤ X)
    (hX1 : X ≤ 78541 / 100000) (hy : |value y1.toBits| ≤ X / 2 ^ 52)
    (har : |value y0.toBits + value y1.toBits - r| ≤ |r| / 2 ^ 59) :
    F64SignedRounding.WithinSteps 1 (if odd then -1 / Real.tan r else Real.tan r)
      (Tan.kernelTan y0 y1 odd).toBits := by
  have hix := TrigSinCos.high_word y0.toBits
  have habs := abs_toNat y0.toBits
  have hav := abs_value y0.toBits
  have hfin := finite_bound y0.toBits f0
  obtain ⟨-, t1⟩ := thresholds
  have hA63 : (Wasm.IEEE64.abs y0.toBits).toNat < 2 ^ 63 := by rw [habs]; omega
  by_cases hb : ((y0.toBits >>> 32) &&& 0x7fffffff) ≥ 0x3FE59428
  · rw [kernelTan_big_bits _ _ _ hb]
    have hb' : 1072010280 ≤ y0.toBits.toNat % 2 ^ 63 / 2 ^ 32 := by
      have := UInt64.le_iff_toNat_le.mp hb
      rw [hix] at this
      exact this
    have hlo : 1414184 / 2 ^ 21 ≤ X := by
      rw [← hX, ← hav, ← t1]
      exact (F64PositiveOrder.value_le_iff (by decide) hA63).mpr (by
        rw [habs]
        show 0x3FE5942800000000 ≤ _
        omega)
    exact big_within _ _ odd r X f0 f1 hX (le_trans (by norm_num) hlo) hX1 hy har
  · rw [kernelTan_small_bits _ _ _ hb]
    have hb' : y0.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 1072010280 := by
      have := mt UInt64.le_iff_toNat_le.mpr hb
      rw [hix, show (0x3FE59428 : UInt64).toNat = 1072010280 from rfl] at this
      omega
    have hhi : X < 1414184 / 2 ^ 21 := by
      rw [← hX, ← hav, ← t1]
      exact F64PositiveOrder.value_strict (by decide) (by
        rw [habs]
        show _ < 0x3FE5942800000000
        omega)
    have hX1' : X ≤ 67434 / 100000 := le_trans hhi.le (by norm_num)
    cases odd
    · rw [smallW_even]
      simpa using even_within _ _ r X f0 f1 hX hX0 hX1' hy har
    · rw [smallW_odd]
      simpa using odd_within _ _ r X f0 f1 hX hX0 hX1' hy har

/-- `tan (r + N π/2)` from `tan r`. -/
theorem tan_quadrant (r : ℝ) (N : Int) (k : Nat) (hk : (k : Int) = N % 4) :
    Real.tan (r + N * (Real.pi / 2)) = if k % 2 = 1 then -1 / Real.tan r else Real.tan r := by
  obtain ⟨h0, h1, h2, h3⟩ := TrigQuadrant.quadrant r N k hk
  have hk4 : k < 4 := by omega
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  interval_cases k
  · rw [(h0 rfl).1, (h0 rfl).2]
    rfl
  · rw [(h1 rfl).1, (h1 rfl).2, if_pos rfl, div_neg, neg_div, one_div_div]
  · rw [(h2 rfl).1, (h2 rfl).2, if_neg (by decide), neg_div_neg_eq]
  · rw [(h3 rfl).1, (h3 rfl).2, if_pos rfl, neg_div, neg_div, one_div_div]

theorem odd_beq (n : UInt64) : (n &&& 1 == 1) = decide (n.toNat % 4 % 2 = 1) := by
  have h : (n &&& 1).toNat = n.toNat % 2 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod n.toNat 1
  by_cases hc : n &&& 1 = 1
  · rw [beq_iff_eq.mpr hc]
    have : n.toNat % 2 = 1 := by rw [← h, hc]; rfl
    exact (decide_eq_true (by omega)).symm
  · have h' : n.toNat % 2 ≠ 1 := fun h' => hc (UInt64.toNat_inj.mp (by rw [h, h']; rfl))
    rw [beq_eq_false_iff_ne.mpr hc, decide_eq_false (by omega)]

/-- The kernel on a reduced argument gives `tan` of the argument before the reduction. -/
theorem reduced_tan (xa n : UInt64) (y0 y1 : Float) (hR : Reduced xa n y0.toBits y1.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.tan (value xa))
      (Tan.kernelTan y0 y1 (n &&& 1 == 1)).toBits := by
  obtain ⟨N, hN, f0, f1, hacc, htail, hrl, hru⟩ := hR
  set r := value xa - N * (Real.pi / 2) with hr
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hsum := abs_le.mp hacc
  have hrr : |r| / 2 ^ 60 ≤ |r| := div_le_self (abs_nonneg _) (by norm_num)
  have h1 := abs_add_le (value y0.toBits + value y1.toBits) (-(value y1.toBits))
  rw [show value y0.toBits + value y1.toBits + -value y1.toBits = value y0.toBits by ring,
    abs_neg] at h1
  have h2 : |value y0.toBits + value y1.toBits| ≤ |r| + |r| / 2 ^ 60 := by
    have := abs_sub_abs_le_abs_sub (value y0.toBits + value y1.toBits) r
    linarith
  have h2' : |r| - |r| / 2 ^ 60 ≤ |value y0.toBits + value y1.toBits| := by
    have := abs_sub_abs_le_abs_sub r (value y0.toBits + value y1.toBits)
    have hc : |r - (value y0.toBits + value y1.toBits)| =
        |value y0.toBits + value y1.toBits - r| := abs_sub_comm _ _
    linarith
  have h3 := abs_add_le (value y0.toBits) (value y1.toBits)
  have hlo : 1 / 2 ^ 70 ≤ |value y0.toBits| := by
    have : |r| * (1 - 1 / 2 ^ 60) ≤ |value y0.toBits| * (1 + 1 / 2 ^ 52) := by linarith
    have : (1 : ℝ) / 2 ^ 63 * (1 - 1 / 2 ^ 60) ≤ |r| * (1 - 1 / 2 ^ 60) :=
      mul_le_mul_of_nonneg_right hrl (by norm_num)
    have : |value y0.toBits| * (1 + 1 / 2 ^ 52) ≤ |value y0.toBits| * 2 :=
      mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    have : (1 : ℝ) / 2 ^ 70 * 2 ≤ 1 / 2 ^ 63 * (1 - 1 / 2 ^ 60) := by norm_num
    linarith
  have hX1 : |value y0.toBits| ≤ 78541 / 100000 := by
    have : |value y0.toBits| * (1 - 1 / 2 ^ 52) ≤ |r| * (1 + 1 / 2 ^ 60) := by linarith
    have : ((3.1416 : ℝ) / 4 + 1 / 2 ^ 17) * (1 + 1 / 2 ^ 60) ≤
        78541 / 100000 * (1 - 1 / 2 ^ 52) := by
      norm_num
    have : |r| * (1 + 1 / 2 ^ 60) ≤ (3.1416 / 4 + 1 / 2 ^ 17) * (1 + 1 / 2 ^ 60) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have har : |value y0.toBits + value y1.toBits - r| ≤ |r| / 2 ^ 59 :=
    hacc.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num))
  have hk := kernel_within y0 y1 (n &&& 1 == 1) r _ f0 f1 rfl hlo hX1 htail har
  have hk4 : ((n.toNat % 4 : Nat) : Int) = N % 4 := by push_cast; exact hN
  have hq := tan_quadrant r N (n.toNat % 4) hk4
  rw [show r + N * (Real.pi / 2) = value xa by rw [hr]; ring] at hq
  rw [hq, odd_beq]
  rw [odd_beq] at hk
  by_cases hp : n.toNat % 4 % 2 = 1
  · rw [if_pos hp, decide_eq_true hp]
    rw [decide_eq_true hp] at hk
    simpa using hk
  · rw [if_neg hp, decide_eq_false hp]
    rw [decide_eq_false hp] at hk
    simpa using hk

/-- The accuracy of `Tan.tan` for every finite `x`. -/
theorem tan_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.tan (value x.toBits)) (Tan.tan x).toBits := by
  have hix := TrigSinCos.high_word x.toBits
  have hfin := finite_bound x.toBits hxf
  have habs := abs_toNat x.toBits
  have hav := abs_value x.toBits
  obtain ⟨t27, t59⟩ := thresholds
  obtain ⟨-, t21, -⟩ := threshold_values
  obtain ⟨-, -, -, -, -, h0f⟩ := finite_words
  have hA63 : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [habs]; omega
  unfold Tan.tan Tan.tanWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  by_cases h1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 ≤ 1072243195
  · rw [if_pos h1]
    by_cases h2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 1044381696
    · have hsmall : |value x.toBits| < 1 / 2 ^ 27 := by
        rw [← hav, ← t27]
        exact F64PositiveOrder.value_strict (by decide) (by
          rw [habs]
          show _ < 0x3E40000000000000
          omega)
      have hu0 := toUInt64_small x hxf (lt_trans hsmall (by norm_num))
      rw [if_pos (by rw [hu0, decide_eq_true h2]; rfl)]
      exact tiny_tan x.toBits hxf hsmall (zero_iff x.toBits)
    · rw [if_neg (by rw [decide_eq_false h2]; simp)]
      have hlo : 1 / 2 ^ 27 ≤ |value x.toBits| := by
        rw [← hav, ← t27]
        exact (F64PositiveOrder.value_le_iff (by decide) hA63).mpr (by
          rw [habs]
          show 0x3E40000000000000 ≤ _
          omega)
      have hhi : |value x.toBits| < 1647100 / 2 ^ 21 := by
        rw [← hav, ← t21]
        exact F64PositiveOrder.value_strict (by decide) (by
          rw [habs]
          show _ < 0x3FE921FC00000000
          omega)
      have hk := kernel_within x 0.0 false (value x.toBits) |value x.toBits| hxf
        (by rw [zero_toBits]; exact h0f) rfl (le_trans (by norm_num) hlo)
        (le_trans hhi.le (by norm_num))
        (by rw [zero_toBits, value_zero, abs_zero]; positivity)
        (by rw [zero_toBits, value_zero, add_zero, sub_self, abs_zero]; positivity)
      simpa using hk
  · rw [if_neg h1]
    have h3 : ¬ (2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32) := by omega
    rw [if_neg h3]
    have hR := TrigReduce.remPio2_spec x.abs (by rw [F64Bits.toBits_abs]; exact hA63)
      (by rw [F64Bits.toBits_abs, habs]; omega) (by rw [F64Bits.toBits_abs, habs]; omega)
    generalize Trig.remPio2 Trig.invPi Trig.halfPi x.abs = P at hR ⊢
    obtain ⟨n, y0, y1⟩ := P
    dsimp only at hR ⊢
    rw [F64Bits.toBits_abs] at hR
    have hsel := reduced_tan _ n y0 y1 hR
    rw [hav] at hsel
    by_cases hneg : x < 0.0
    · have hv := (lt_zero_iff x hxf).mp hneg
      rw [if_pos hneg]
      rw [abs_of_neg hv, Real.tan_neg] at hsel
      have := neg_within _ _ hsel
      rwa [neg_neg] at this
    · have hv : 0 ≤ value x.toBits := not_lt.mp (fun h => hneg ((lt_zero_iff x hxf).mpr h))
      rw [if_neg hneg]
      rwa [abs_of_nonneg hv] at hsel

#print axioms tan_within

end Verified.Examples.TanWith
