import Project.ProofKit.F64DyadicBounds
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64MulBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem product_abs_scaled (a b : UInt64) :
    |value a * value b| =
      ((Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b : Nat) : ℝ) /
        (2 : ℝ)^2148 := by
  have hscaledAbs (x : UInt64) :
      |(Wasm.IEEE64.scaledValue x : ℝ)| =
        (Wasm.IEEE64.scaledMagnitude x : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_scaledValue]
    norm_num
  simp [value, abs_mul, abs_div, hscaledAbs]
  ring

theorem mul_scaled_adaptive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b < 2^3170) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul a b) * (2 : Int)^1074 -
      Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b| * (2^53 : Int) ≤
      (let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
        if n = 0 then 0 else max n (2^1126) : Nat) := by
  let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
  have hs := F64DyadicBounds.dyadic_relative
    (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n hbound
  rw [mul_finite_rounder a b ha hb]
  refine ⟨hs.1, ?_⟩
  have herr := hs.2.2
  have hresultSign := hs.2.1
  have habs (x y : Int) : |-x + y| = |x + -y| := by
    rw [show -x + y = -(x + -y) by ring, abs_neg]
  cases hsa : Wasm.IEEE64.sign a <;>
    cases hsb : Wasm.IEEE64.sign b <;>
    simp [n, hsa, hsb] at hresultSign <;>
    simp [Wasm.IEEE64.scaledValue, hresultSign, hsa, hsb, n] at herr ⊢
  all_goals
    first
    | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
    | rw [habs]
      simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

theorem mul_real_adaptive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a * value b| < (2 : ℝ)^1022) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
      unitRoundoff64 *
        (let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
          if n = 0 then 0 else max |value a * value b| minNormal64) := by
  let n := Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b
  have hproductAbs : |value a * value b| = (n : ℝ) / (2 : ℝ)^2148 :=
    product_abs_scaled a b
  have hn : n < 2^3170 := by
    rw [hproductAbs] at hbound
    have hs := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^2148)).mp hbound
    rw [← pow_add] at hs
    exact_mod_cast hs
  have hs := mul_scaled_adaptive a b ha hb hn
  refine ⟨hs.1, ?_⟩
  let z : Int := Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul a b) * (2 : Int)^1074 -
    Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b
  have hz : |z| * (2^53 : Int) ≤
      (if n = 0 then 0 else max n (2^1126) : Nat) := hs.2
  have hzReal : |(z : ℝ)| * (2 : ℝ)^53 ≤
      ((if n = 0 then 0 else max n (2^1126) : Nat) : ℝ) := by
    exact_mod_cast hz
  have heq : value (Wasm.IEEE64.mul a b) - value a * value b =
      (z : ℝ) / (2 : ℝ)^2148 := by
    simp [value, z]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^2148)]
  calc
    |(z : ℝ)| / (2 : ℝ)^2148 =
        (|(z : ℝ)| * (2 : ℝ)^53) / ((2 : ℝ)^53 * (2 : ℝ)^2148) := by field_simp
    _ ≤ ((if n = 0 then 0 else max n (2^1126) : Nat) : ℝ) /
        ((2 : ℝ)^53 * (2 : ℝ)^2148) :=
      div_le_div_of_nonneg_right hzReal (by positivity)
    _ = unitRoundoff64 *
        (if n = 0 then 0 else max |value a * value b| minNormal64) := by
      by_cases hn0 : n = 0
      · simp [hn0, unitRoundoff64]
      · simp only [hn0, if_false, hproductAbs]
        have hnormal : minNormal64 = (2 : ℝ)^1126 / (2 : ℝ)^2148 := by
          norm_num [minNormal64]
        rw [hnormal, max_div_div_right (show 0 ≤ (2 : ℝ)^2148 by positivity)]
        simp only [Nat.cast_max, Nat.cast_pow, Nat.cast_ofNat]
        norm_num [unitRoundoff64, minNormal64]
        ring

theorem mul_real_mixed (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hbound : |value a * value b| < (2 : ℝ)^1022) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
      unitRoundoff64 * |value a * value b| + multiplicationUnderflowEpsilon := by
  have hs := mul_real_adaptive a b ha hb hbound
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hp := abs_nonneg (value a * value b)
  have hm : 0 ≤ minNormal64 := by norm_num [minNormal64]
  have hepsilon : 0 ≤ multiplicationUnderflowEpsilon := by
    norm_num [multiplicationUnderflowEpsilon]
  dsimp only
  split
  · simp only [mul_zero]
    exact add_nonneg (mul_nonneg hu hp) hepsilon
  · calc
      unitRoundoff64 * max |value a * value b| minNormal64 ≤
          unitRoundoff64 * (|value a * value b| + minNormal64) :=
        mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hu
      _ = unitRoundoff64 * |value a * value b| + multiplicationUnderflowEpsilon := by
        rw [mul_add]
        congr 1
        norm_num [unitRoundoff64, minNormal64, multiplicationUnderflowEpsilon]

#print axioms mul_scaled_adaptive
#print axioms mul_real_adaptive
#print axioms mul_real_mixed
end Project.ProofKit.F64MulBounds
