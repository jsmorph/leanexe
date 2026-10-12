import Verified.Examples.FourierProduct
import Verified.Examples.FFTComplex
import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64Bits
import Mathlib.Analysis.Complex.Basic

namespace Verified.Examples.FFTArithmetic

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx

noncomputable def q : ℝ := (1 + unitRoundoff64) ^ 2 * (1 + 32 * unitRoundoff64)
noncomputable def r : ℝ := (1 + unitRoundoff64) * (2 * q - 1)
noncomputable def nu : ℝ :=
  3 * (1 + unitRoundoff64) ^ 2 * multiplicationUnderflowEpsilon

noncomputable def pairValue (a : Float × Float) : ℂ :=
  ⟨value a.1.toBits, value a.2.toBits⟩

def PairFinite (a : Float × Float) : Prop := Finite a.1.toBits ∧ Finite a.2.toBits

def product (b factor : Float × Float) : Float × Float :=
  (b.1 * factor.1 - b.2 * factor.2, b.1 * factor.2 + b.2 * factor.1)

def add (a b : Float × Float) : Float × Float := (a.1 + b.1, a.2 + b.2)

def sub (a b : Float × Float) : Float × Float := (a.1 - b.1, a.2 - b.2)

def butterfly (a b factor : Float × Float) : (Float × Float) × (Float × Float) :=
  let t := product b factor
  (add a t, sub a t)

theorem unit_nonneg : 0 ≤ unitRoundoff64 := by
  unfold unitRoundoff64
  positivity

theorem eta_nonneg : 0 ≤ multiplicationUnderflowEpsilon := by
  unfold multiplicationUnderflowEpsilon
  positivity

theorem nu_nonneg : 0 ≤ nu := by
  unfold nu
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) eta_nonneg

theorem q_ge_one : 1 ≤ q := by
  have hu := unit_nonneg
  have hpow : 1 ≤ (1 + unitRoundoff64) ^ 2 := one_le_pow₀ (by linarith)
  unfold q
  nlinarith

theorem r_ge_one : 1 ≤ r := by
  have hu := unit_nonneg
  have hq := q_ge_one
  unfold r
  nlinarith

theorem r_minus_one_ge_unit : unitRoundoff64 ≤ r - 1 := by
  have hu := unit_nonneg
  have hq := q_ge_one
  unfold r
  nlinarith

theorem product_safe_bound (b : Float × Float) (B : ℝ) (hb : ‖pairValue b‖ ≤ B) :
    FourierProduct.productMagnitude (value b.1.toBits) (value b.2.toBits) ≤
      2 * q * B + 2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon := by
  have hq0 : 0 ≤ q := zero_le_one.trans q_ge_one
  have hab : |value b.1.toBits| + |value b.2.toBits| ≤ 2 * B := by
    have hr := Complex.abs_re_le_norm (pairValue b)
    have hi := Complex.abs_im_le_norm (pairValue b)
    change |value b.1.toBits| ≤ ‖pairValue b‖ at hr
    change |value b.2.toBits| ≤ ‖pairValue b‖ at hi
    linarith
  change q * (|value b.1.toBits| + |value b.2.toBits|) + _ ≤ _
  calc
    _ ≤ q * (2 * B) + 2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon :=
      add_le_add (mul_le_mul_of_nonneg_left hab hq0) le_rfl
    _ = _ := by ring

theorem complex_product_near (b factor : Float × Float) (w : ℂ)
    (hb : PairFinite b)
    (hc : FApprox factor.1 w.re (32 * unitRoundoff64))
    (hd : FApprox factor.2 w.im (32 * unitRoundoff64)) (hw : ‖w‖ = 1)
    (hsafe : FourierProduct.productMagnitude (value b.1.toBits) (value b.2.toBits) <
      (2 : ℝ) ^ 1022) :
    PairFinite (product b factor) ∧
      ‖pairValue (product b factor) - pairValue b * w‖ ≤
        2 * (q - 1) * ‖pairValue b‖ +
          3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon := by
  have hC : |w.re| ≤ 1 := by simpa only [hw] using Complex.abs_re_le_norm w
  have hD : |w.im| ≤ 1 := by simpa only [hw] using Complex.abs_im_le_norm w
  have hr := FourierProduct.sub_near b.1 b.2 factor.1 factor.2 w.re w.im
    hb.1 hb.2 hc hd hC hD hsafe
  have hi := FourierProduct.add_near b.1 b.2 factor.2 factor.1 w.im w.re
    hb.1 hb.2 hd hc hD hC hsafe
  refine ⟨⟨hr.1, hi.1⟩, ?_⟩
  have hnorm := FFTComplex.product_error_norm (pairValue b)
    (pairValue (product b factor) - pairValue b * w) q
    ((1 + unitRoundoff64) * multiplicationUnderflowEpsilon) q_ge_one
    (mul_nonneg (by linarith [unit_nonneg]) eta_nonneg)
    (by simpa only [pairValue, product, Complex.sub_re, Complex.mul_re,
      FourierProduct.productError, q, mul_assoc] using hr.2)
    (by simpa only [pairValue, product, Complex.sub_im, Complex.mul_im,
      FourierProduct.productError, q, mul_comm, mul_assoc, add_comm] using hi.2)
  simpa only [mul_assoc] using hnorm

theorem complex_product_coordinate_bounds (b factor : Float × Float) (w : ℂ)
    (hb : PairFinite b)
    (hc : FApprox factor.1 w.re (32 * unitRoundoff64))
    (hd : FApprox factor.2 w.im (32 * unitRoundoff64)) (hw : ‖w‖ = 1)
    (hsafe : FourierProduct.productMagnitude (value b.1.toBits) (value b.2.toBits) <
      (2 : ℝ) ^ 1022) :
    |(pairValue (product b factor)).re| ≤
      FourierProduct.productMagnitude (value b.1.toBits) (value b.2.toBits) ∧
    |(pairValue (product b factor)).im| ≤
      FourierProduct.productMagnitude (value b.1.toBits) (value b.2.toBits) := by
  have hC : |w.re| ≤ 1 := by simpa only [hw] using Complex.abs_re_le_norm w
  have hD : |w.im| ≤ 1 := by simpa only [hw] using Complex.abs_im_le_norm w
  exact ⟨FourierProduct.sub_magnitude _ _ _ _ _ _ hb.1 hb.2 hc hd hC hD hsafe,
    FourierProduct.add_magnitude _ _ _ _ _ _ hb.1 hb.2 hd hc hD hC hsafe⟩

theorem complex_add_near (a b : Float × Float) (ha : PairFinite a) (hb : PairFinite b)
    (hr : |(pairValue a + pairValue b).re| < (2 : ℝ) ^ 1023)
    (hi : |(pairValue a + pairValue b).im| < (2 : ℝ) ^ 1023) :
    PairFinite (add a b) ∧
      ‖pairValue (add a b) - (pairValue a + pairValue b)‖ ≤
        unitRoundoff64 * ‖pairValue a + pairValue b‖ := by
  have hre := F64AddBounds.add_real_relative a.1.toBits b.1.toBits ha.1 hb.1 hr
  have him := F64AddBounds.add_real_relative a.2.toBits b.2.toBits ha.2 hb.2 hi
  rw [← F64Bits.toBits_add] at hre him
  refine ⟨⟨hre.1, him.1⟩, ?_⟩
  apply FFTComplex.norm_le_of_coordinate_relative _ _ unitRoundoff64 unit_nonneg
  · exact hre.2
  · exact him.2

theorem complex_sub_near (a b : Float × Float) (ha : PairFinite a) (hb : PairFinite b)
    (hr : |(pairValue a - pairValue b).re| < (2 : ℝ) ^ 1023)
    (hi : |(pairValue a - pairValue b).im| < (2 : ℝ) ^ 1023) :
    PairFinite (sub a b) ∧
      ‖pairValue (sub a b) - (pairValue a - pairValue b)‖ ≤
        unitRoundoff64 * ‖pairValue a - pairValue b‖ := by
  have hre := F64AddBounds.sub_real_relative a.1.toBits b.1.toBits ha.1 hb.1 hr
  have him := F64AddBounds.sub_real_relative a.2.toBits b.2.toBits ha.2 hb.2 hi
  rw [← F64Bits.toBits_sub] at hre him
  refine ⟨⟨hre.1, him.1⟩, ?_⟩
  apply FFTComplex.norm_le_of_coordinate_relative _ _ unitRoundoff64 unit_nonneg
  · exact hre.2
  · exact him.2

theorem butterfly_result_bounds (a b t out a0 b0 w sign : ℂ) (Ea Eb : ℝ)
    (hw : ‖w‖ = 1) (hsign : ‖sign‖ = 1)
    (ha : ‖a - a0‖ ≤ Ea) (hb : ‖b - b0‖ ≤ Eb)
    (ht : ‖t - b * w‖ ≤ 2 * (q - 1) * ‖b‖ +
      3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon)
    (hout : ‖out - (a + sign * t)‖ ≤ unitRoundoff64 * ‖a + sign * t‖) :
    ‖out‖ ≤ r * (‖a‖ + ‖b‖) + nu ∧
      ‖out - (a0 + sign * (b0 * w))‖ ≤
        Ea + Eb + (r - 1) * (‖a‖ + ‖b‖) + nu := by
  have hu1 : 0 ≤ 1 + unitRoundoff64 := by linarith [unit_nonneg]
  have hrunit : 1 + unitRoundoff64 ≤ r := by linarith [r_minus_one_ge_unit]
  have hnormt : ‖t‖ ≤ (2 * q - 1) * ‖b‖ +
      3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon := by
    calc
      ‖t‖ = ‖(t - b * w) + b * w‖ := by congr 1; ring
      _ ≤ ‖t - b * w‖ + ‖b * w‖ := norm_add_le _ _
      _ ≤ (2 * (q - 1) * ‖b‖ +
          3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon) + ‖b‖ := by
        rw [norm_mul, hw, mul_one]
        exact add_le_add ht le_rfl
      _ = _ := by ring
  have hnormsum : ‖a + sign * t‖ ≤ ‖a‖ + ‖t‖ := by
    simpa only [norm_mul, hsign, one_mul] using norm_add_le a (sign * t)
  have htarget : ‖(a + sign * t) - (a0 + sign * (b0 * w))‖ ≤
      Ea + Eb + (2 * (q - 1) * ‖b‖ +
        3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon) := by
    rw [show (a + sign * t) - (a0 + sign * (b0 * w)) =
      (a - a0) + sign * ((t - b * w) + (b - b0) * w) by ring]
    calc
      _ ≤ ‖a - a0‖ + ‖sign * ((t - b * w) + (b - b0) * w)‖ := norm_add_le _ _
      _ = ‖a - a0‖ + ‖(t - b * w) + (b - b0) * w‖ := by rw [norm_mul, hsign, one_mul]
      _ ≤ Ea + (‖t - b * w‖ + ‖(b - b0) * w‖) :=
        add_le_add ha (norm_add_le _ _)
      _ ≤ Ea + ((2 * (q - 1) * ‖b‖ +
          3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon) + Eb) := by
        rw [norm_mul, hw, mul_one]
        exact add_le_add le_rfl (add_le_add ht hb)
      _ = _ := by ring
  constructor
  · calc
      ‖out‖ = ‖(out - (a + sign * t)) + (a + sign * t)‖ := by congr 1; ring
      _ ≤ ‖out - (a + sign * t)‖ + ‖a + sign * t‖ := norm_add_le _ _
      _ ≤ unitRoundoff64 * ‖a + sign * t‖ + ‖a + sign * t‖ := add_le_add hout le_rfl
      _ = (1 + unitRoundoff64) * ‖a + sign * t‖ := by ring
      _ ≤ (1 + unitRoundoff64) * (‖a‖ + ‖t‖) :=
        mul_le_mul_of_nonneg_left hnormsum hu1
      _ ≤ (1 + unitRoundoff64) * (‖a‖ + ((2 * q - 1) * ‖b‖ +
          3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hnormt) hu1
      _ = (1 + unitRoundoff64) * ‖a‖ + r * ‖b‖ + nu := by unfold r nu; ring
      _ ≤ r * ‖a‖ + r * ‖b‖ + nu :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hrunit (norm_nonneg a)) le_rfl) le_rfl
      _ = _ := by ring
  · calc
      ‖out - (a0 + sign * (b0 * w))‖ =
          ‖(out - (a + sign * t)) + ((a + sign * t) - (a0 + sign * (b0 * w)))‖ := by
        congr 1
        ring
      _ ≤ ‖out - (a + sign * t)‖ + ‖(a + sign * t) - (a0 + sign * (b0 * w))‖ :=
        norm_add_le _ _
      _ ≤ unitRoundoff64 * ‖a + sign * t‖ +
          (Ea + Eb + (2 * (q - 1) * ‖b‖ +
            3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon)) :=
        add_le_add hout htarget
      _ ≤ unitRoundoff64 * (‖a‖ + ‖t‖) +
          (Ea + Eb + (2 * (q - 1) * ‖b‖ +
            3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon)) :=
        add_le_add (mul_le_mul_of_nonneg_left hnormsum unit_nonneg) le_rfl
      _ ≤ unitRoundoff64 * (‖a‖ + ((2 * q - 1) * ‖b‖ +
          3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon)) +
          (Ea + Eb + (2 * (q - 1) * ‖b‖ +
            3 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon)) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hnormt) unit_nonneg) le_rfl
      _ = Ea + Eb + unitRoundoff64 * ‖a‖ + (r - 1) * ‖b‖ + nu := by unfold r nu; ring
      _ ≤ Ea + Eb + (r - 1) * ‖a‖ + (r - 1) * ‖b‖ + nu := by
        gcongr
        exact r_minus_one_ge_unit
      _ = _ := by ring

theorem butterfly_near (a b factor : Float × Float) (w a0 b0 : ℂ) (Ea Eb B : ℝ)
    (ha : PairFinite a) (hb : PairFinite b)
    (hc : FApprox factor.1 w.re (32 * unitRoundoff64))
    (hd : FApprox factor.2 w.im (32 * unitRoundoff64)) (hw : ‖w‖ = 1)
    (hnorma : ‖pairValue a‖ ≤ B) (hnormb : ‖pairValue b‖ ≤ B)
    (hsafe : 2 * q * B + 2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon <
      (2 : ℝ) ^ 1022)
    (ha0 : ‖pairValue a - a0‖ ≤ Ea) (hb0 : ‖pairValue b - b0‖ ≤ Eb) :
    PairFinite (butterfly a b factor).1 ∧ PairFinite (butterfly a b factor).2 ∧
      ‖pairValue (butterfly a b factor).1‖ ≤ r * (‖pairValue a‖ + ‖pairValue b‖) + nu ∧
      ‖pairValue (butterfly a b factor).2‖ ≤ r * (‖pairValue a‖ + ‖pairValue b‖) + nu ∧
      ‖pairValue (butterfly a b factor).1 - (a0 + b0 * w)‖ ≤
        Ea + Eb + (r - 1) * (‖pairValue a‖ + ‖pairValue b‖) + nu ∧
      ‖pairValue (butterfly a b factor).2 - (a0 - b0 * w)‖ ≤
        Ea + Eb + (r - 1) * (‖pairValue a‖ + ‖pairValue b‖) + nu := by
  let t := product b factor
  let P := 2 * q * B + 2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon
  have hP : P < (2 : ℝ) ^ 1022 := hsafe
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hnorma
  have hq0 : 0 ≤ q := zero_le_one.trans q_ge_one
  have hB : B ≤ P := by
    have hqB : B ≤ q * B := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right q_ge_one hB0
    have hqB0 : 0 ≤ q * B := mul_nonneg hq0 hB0
    have he0 : 0 ≤ 2 * (1 + unitRoundoff64) * multiplicationUnderflowEpsilon :=
      mul_nonneg (by linarith [unit_nonneg]) eta_nonneg
    dsimp only [P]
    nlinarith only [hqB, hqB0, he0]
  have hmargin : B + P < (2 : ℝ) ^ 1023 := by
    calc
      B + P ≤ P + P := add_le_add hB le_rfl
      _ = 2 * P := by ring
      _ < 2 * (2 : ℝ) ^ 1022 := mul_lt_mul_of_pos_left hP (by norm_num)
      _ = (2 : ℝ) ^ 1023 := by
        rw [show (2 : ℝ) ^ 1023 = (2 : ℝ) ^ 1022 * 2 from pow_succ _ _]
        ring
  have hproductB := product_safe_bound b B hnormb
  have hproductSafe := hproductB.trans_lt hsafe
  have ht := complex_product_near b factor w hb hc hd hw hproductSafe
  have hcoord := complex_product_coordinate_bounds b factor w hb hc hd hw hproductSafe
  have hAr : |(pairValue a).re| ≤ B := (Complex.abs_re_le_norm _).trans hnorma
  have hAi : |(pairValue a).im| ≤ B := (Complex.abs_im_le_norm _).trans hnorma
  have hTr : |(pairValue t).re| ≤ P := hcoord.1.trans hproductB
  have hTi : |(pairValue t).im| ≤ P := hcoord.2.trans hproductB
  have hadd := complex_add_near a t ha ht.1
    (((abs_add_le _ _).trans (add_le_add hAr hTr)).trans_lt hmargin)
    (((abs_add_le _ _).trans (add_le_add hAi hTi)).trans_lt hmargin)
  have hsub := complex_sub_near a t ha ht.1
    (((abs_sub _ _).trans (add_le_add hAr hTr)).trans_lt hmargin)
    (((abs_sub _ _).trans (add_le_add hAi hTi)).trans_lt hmargin)
  have hplus := butterfly_result_bounds (pairValue a) (pairValue b) (pairValue t)
    (pairValue (add a t)) a0 b0 w 1 Ea Eb hw (by simp) ha0 hb0 ht.2
    (by simpa only [one_mul] using hadd.2)
  have hminus := butterfly_result_bounds (pairValue a) (pairValue b) (pairValue t)
    (pairValue (sub a t)) a0 b0 w (-1) Ea Eb hw (by simp) ha0 hb0 ht.2
    (by simpa only [neg_one_mul, sub_eq_add_neg] using hsub.2)
  exact ⟨hadd.1, hsub.1, hplus.1, hminus.1,
    by simpa only [butterfly, t, one_mul] using hplus.2,
    by simpa only [butterfly, t, neg_one_mul, sub_eq_add_neg] using hminus.2⟩

theorem next_stage_magnitude (s : Nat) (Aa Ab K Ma Mb : ℝ)
    (ha : Ma ≤ r ^ s * Aa + K) (hb : Mb ≤ r ^ s * Ab + K) :
    r * (Ma + Mb) + nu ≤ r ^ (s + 1) * (Aa + Ab) + (2 * r * K + nu) := by
  calc
    _ ≤ r * ((r ^ s * Aa + K) + (r ^ s * Ab + K)) + nu :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add ha hb) (zero_le_one.trans r_ge_one)) le_rfl
    _ = _ := by rw [pow_succ]; ring

theorem next_stage_error (s : Nat) (Aa Ab K Ma Mb Ea Eb : ℝ)
    (hma : Ma ≤ r ^ s * Aa + K) (hmb : Mb ≤ r ^ s * Ab + K)
    (hea : Ea ≤ (r ^ s - 1) * Aa + K) (heb : Eb ≤ (r ^ s - 1) * Ab + K) :
    Ea + Eb + (r - 1) * (Ma + Mb) + nu ≤
      (r ^ (s + 1) - 1) * (Aa + Ab) + (2 * r * K + nu) := by
  calc
    _ ≤ ((r ^ s - 1) * Aa + K) + ((r ^ s - 1) * Ab + K) +
        (r - 1) * ((r ^ s * Aa + K) + (r ^ s * Ab + K)) + nu :=
      add_le_add (add_le_add (add_le_add hea heb)
        (mul_le_mul_of_nonneg_left (add_le_add hma hmb) (sub_nonneg.mpr r_ge_one))) le_rfl
    _ = _ := by rw [pow_succ]; ring

#print axioms complex_product_near
#print axioms complex_product_coordinate_bounds
#print axioms complex_add_near
#print axioms complex_sub_near
#print axioms butterfly_result_bounds
#print axioms butterfly_near
#print axioms next_stage_magnitude
#print axioms next_stage_error

end Verified.Examples.FFTArithmetic
