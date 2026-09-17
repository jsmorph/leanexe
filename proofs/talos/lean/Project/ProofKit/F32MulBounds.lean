import Project.ProofKit.F32DyadicBounds
import CodeLib.IEEE32.Multiplication
import Project.ProofKit.F32AddBounds

namespace Project.ProofKit.F32MulBounds
open CodeLib.IEEE32

set_option exponentiation.threshold 512

noncomputable def minNormal : ℝ := 1 / (2:ℝ)^126
noncomputable def multiplicationUnderflowEpsilon : ℝ := 1 / (2:ℝ)^150

theorem product_abs_scaled (a b : UInt32) :
    |value a * value b| =
      ((Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b : Nat) : ℝ) /
        (2 : ℝ)^298 := by
  have hscaledAbs (x : UInt32) :
      |(Wasm.IEEE32.scaledValue x : ℝ)| =
        (Wasm.IEEE32.scaledMagnitude x : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_scaledValue]
    norm_num
  simp [value, abs_mul, abs_div, hscaledAbs]
  ring

theorem mul_scaled_adaptive (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2^425) :
    Finite (Wasm.IEEE32.mul a b) ∧
    |Wasm.IEEE32.scaledValue (Wasm.IEEE32.mul a b) * (2 : Int)^149 -
      Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b| * (2^24 : Int) ≤
      (let n := Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b;
        max n (2^172) : Nat) := by
  let n := Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b
  have hs := F32DyadicBounds.dyadic_relative
    (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b) n 149 (by decide) hbound
  rw [mul_finite_rounder a b ha hb]
  refine ⟨hs.1, ?_⟩
  have herr := hs.2.2
  have hresultSign := hs.2.1
  have habs (x y : Int) : |-x + y| = |x + -y| := by
    rw [show -x + y = -(x + -y) by ring, abs_neg]
  cases hsa : Wasm.IEEE32.sign a <;>
    cases hsb : Wasm.IEEE32.sign b <;>
    simp [n, hsa, hsb] at hresultSign <;>
    simp [Wasm.IEEE32.scaledValue, hresultSign, hsa, hsb, n] at herr ⊢
  all_goals
    first
    | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
    | rw [habs]
      simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

theorem mul_real_adaptive (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : |value a * value b| < (2 : ℝ)^127) :
    Finite (Wasm.IEEE32.mul a b) ∧
    |value (Wasm.IEEE32.mul a b) - value a * value b| ≤
      F32AddBounds.unitRoundoff *
        (max |value a * value b| minNormal) := by
  let n := Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b
  have hproductAbs : |value a * value b| = (n : ℝ) / (2 : ℝ)^298 :=
    product_abs_scaled a b
  have hn : n < 2^425 := by
    rw [hproductAbs] at hbound
    have hs := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^298)).mp hbound
    rw [← pow_add] at hs
    exact_mod_cast hs
  have hs := mul_scaled_adaptive a b ha hb hn
  refine ⟨hs.1, ?_⟩
  let z : Int := Wasm.IEEE32.scaledValue (Wasm.IEEE32.mul a b) * (2 : Int)^149 -
    Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b
  have hz : |z| * (2^24 : Int) ≤
      (max n (2^172) : Nat) := hs.2
  have hzReal : |(z : ℝ)| * (2 : ℝ)^24 ≤
      ((max n (2^172) : Nat) : ℝ) := by
    exact_mod_cast hz
  have heq : value (Wasm.IEEE32.mul a b) - value a * value b =
      (z : ℝ) / (2 : ℝ)^298 := by
    simp [value, z]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^298)]
  calc
    |(z : ℝ)| / (2 : ℝ)^298 =
        (|(z : ℝ)| * (2 : ℝ)^24) / ((2 : ℝ)^24 * (2 : ℝ)^298) := by field_simp
    _ ≤ ((max n (2^172) : Nat) : ℝ) /
        ((2 : ℝ)^24 * (2 : ℝ)^298) :=
      div_le_div_of_nonneg_right hzReal (by positivity)
    _ = F32AddBounds.unitRoundoff *
        (max |value a * value b| minNormal) := by
      rw [hproductAbs]
      have hnormal : minNormal = (2 : ℝ)^172 / (2 : ℝ)^298 := by norm_num [minNormal]
      rw [hnormal, max_div_div_right (show 0 ≤ (2 : ℝ)^298 by positivity)]
      simp only [Nat.cast_max, Nat.cast_pow, Nat.cast_ofNat]
      norm_num [F32AddBounds.unitRoundoff, minNormal]
      ring

theorem mul_real_mixed (a b : UInt32) (ha : Finite a) (hb : Finite b)
    (hbound : |value a * value b| < (2 : ℝ)^127) :
    Finite (Wasm.IEEE32.mul a b) ∧
    |value (Wasm.IEEE32.mul a b) - value a * value b| ≤
      F32AddBounds.unitRoundoff * |value a * value b| + multiplicationUnderflowEpsilon := by
  have hs := mul_real_adaptive a b ha hb hbound
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hu : 0 ≤ F32AddBounds.unitRoundoff := by norm_num [F32AddBounds.unitRoundoff]
  have hp := abs_nonneg (value a * value b)
  have hm : 0 ≤ minNormal := by norm_num [minNormal]
  have hepsilon : 0 ≤ multiplicationUnderflowEpsilon := by
    norm_num [multiplicationUnderflowEpsilon]
  calc
    F32AddBounds.unitRoundoff * max |value a * value b| minNormal ≤
        F32AddBounds.unitRoundoff * (|value a * value b| + minNormal) :=
      mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hu
    _ = F32AddBounds.unitRoundoff * |value a * value b| + multiplicationUnderflowEpsilon := by
      rw [mul_add]
      congr 1
      norm_num [F32AddBounds.unitRoundoff, minNormal, multiplicationUnderflowEpsilon]

#print axioms mul_scaled_adaptive
#print axioms mul_real_adaptive
#print axioms mul_real_mixed
end Project.ProofKit.F32MulBounds
