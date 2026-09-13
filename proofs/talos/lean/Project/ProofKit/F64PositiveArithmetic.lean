import Project.ProofKit.F64ArithmeticBounds
import Project.ProofKit.F64SqrtBounds
import Project.ProofKit.F64OrderComplete

namespace Project.ProofKit.F64PositiveArithmetic
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem positive_input (a : UInt64) (ha : F64Order.positiveBits a = true) :
    Finite a ∧ Wasm.IEEE64.sign a = false ∧ Wasm.IEEE64.scaledMagnitude a ≠ 0 := by
  have hp := F64Order.positiveBits_spec a ha
  have hraw : (0 : UInt64) < a ∧ a < 0x7FF0000000000000 := by
    simpa [F64Order.positiveBits] using ha
  have hhi : a.toNat < 0x7FF0000000000000 := UInt64.lt_iff_toNat_lt.mp hraw.2
  have hsign : Wasm.IEEE64.sign a = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    norm_num at hhi ⊢
    omega
  refine ⟨hp.1, hsign, ?_⟩
  intro hz
  have hv : value a = 0 := by simp [value, Wasm.IEEE64.scaledValue, hz]
  linarith only [hp.2, hv]

theorem normal_relative (rounded exactValue : ℝ) (hmin : minNormal64 ≤ exactValue)
    (herr : |rounded - exactValue| ≤ unitRoundoff64 * exactValue + multiplicationUnderflowEpsilon) :
    |rounded - exactValue| ≤ arithmeticEpsilon * exactValue := by
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have heq : multiplicationUnderflowEpsilon = unitRoundoff64 * minNormal64 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have he := mul_le_mul_of_nonneg_left hmin hu
  rw [← heq] at he
  have heps : arithmeticEpsilon = 2 * unitRoundoff64 := by
    norm_num [arithmeticEpsilon, unitRoundoff64]
  rw [heps]
  linarith only [herr, he]

theorem positive_range (rounded exactValue : ℝ) (hmin : minNormal64 ≤ exactValue)
    (herr : |rounded - exactValue| ≤ unitRoundoff64 * exactValue + multiplicationUnderflowEpsilon) :
    exactValue / 2 ≤ rounded ∧ rounded ≤ 2 * exactValue := by
  have hm : 0 < minNormal64 := by norm_num [minNormal64]
  have hx : 0 < exactValue := hm.trans_le hmin
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have heq : multiplicationUnderflowEpsilon = unitRoundoff64 * minNormal64 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  have he := mul_le_mul_of_nonneg_left hmin hu
  rw [← heq] at he
  have hunit : 2 * unitRoundoff64 ≤ (1 : ℝ) / 2 := by norm_num [unitRoundoff64]
  have hbudget := mul_le_mul_of_nonneg_right hunit hx.le
  have hl := (abs_le.mp herr).1
  have hr := (abs_le.mp herr).2
  constructor <;> nlinarith only [hl, hr, he, hbudget, hx]

theorem mul_positive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hmin : minNormal64 ≤ value a * value b) (hmax : value a * value b < (2 : ℝ)^1022) :
    Finite (Wasm.IEEE64.mul a b) ∧
    value a * value b / 2 ≤ value (Wasm.IEEE64.mul a b) ∧
    value (Wasm.IEEE64.mul a b) ≤ 2 * (value a * value b) := by
  have hp : 0 < value a * value b := lt_of_lt_of_le (by norm_num [minNormal64]) hmin
  have hs := F64MulBounds.mul_real_mixed a b ha hb (by rwa [abs_of_pos hp])
  rw [abs_of_pos hp] at hs
  exact ⟨hs.1, positive_range _ _ hmin hs.2⟩

theorem div_positive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hmin : minNormal64 ≤ value a / value b) (hmax : value a / value b < (2 : ℝ)^1022) :
    Finite (Wasm.IEEE64.div a b) ∧
    (value a / value b) / 2 ≤ value (Wasm.IEEE64.div a b) ∧
    value (Wasm.IEEE64.div a b) ≤ 2 * (value a / value b) := by
  have hp : 0 < value a / value b := lt_of_lt_of_le (by norm_num [minNormal64]) hmin
  have hs := F64DivBounds.div_real_mixed a b ha hb hb0 (by rwa [abs_of_pos hp])
  rw [abs_of_pos hp] at hs
  exact ⟨hs.1, positive_range _ _ hmin hs.2⟩

theorem add_positive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hpos : 0 < value a + value b) (hmax : value a + value b < (2 : ℝ)^1023) :
    F64Order.positiveBits (Wasm.IEEE64.add a b) = true ∧
    (value a + value b) / 2 ≤ value (Wasm.IEEE64.add a b) ∧
    value (Wasm.IEEE64.add a b) ≤ 2 * (value a + value b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
      unitRoundoff64 * (value a + value b) := by
  have hs := F64AddBounds.add_real_relative a b ha hb (by rwa [abs_of_pos hpos])
  rw [abs_of_pos hpos] at hs
  have hu : unitRoundoff64 ≤ (1 : ℝ) / 2 := by norm_num [unitRoundoff64]
  have hb := mul_le_mul_of_nonneg_right hu hpos.le
  have hlo := (abs_le.mp hs.2).1
  have hhi := (abs_le.mp hs.2).2
  have hl : (value a + value b) / 2 ≤ value (Wasm.IEEE64.add a b) := by
    linarith only [hlo, hb]
  have hh : value (Wasm.IEEE64.add a b) ≤ 2 * (value a + value b) := by
    linarith only [hhi, hb, hpos]
  exact ⟨F64Order.positiveBits_of_finite_value_pos _ hs.1
    (lt_of_lt_of_le (by linarith only [hpos]) hl), hl, hh, hs.2⟩

theorem sqrt_positive (a : UInt64) (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hsign : Wasm.IEEE64.sign a = false) :
    F64Order.positiveBits (Wasm.IEEE64.sqrt a) = true ∧
    Real.sqrt (value a) / 2 ≤ value (Wasm.IEEE64.sqrt a) ∧
    value (Wasm.IEEE64.sqrt a) ≤ 2 * Real.sqrt (value a) := by
  have hp : 0 < value a := by
    simp only [value, Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true, ite_false, Int.cast_natCast]
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero ha0) (by positivity)
  have hroot : 0 < Real.sqrt (value a) := Real.sqrt_pos.mpr hp
  have hs := F64SqrtBounds.sqrt_real_relative a ha ha0 hsign
  have hu : unitRoundoff64 ≤ (1 : ℝ) / 2 := by norm_num [unitRoundoff64]
  have he := mul_le_mul_of_nonneg_right hu hroot.le
  have hl := (abs_le.mp hs.2).1
  have hr := (abs_le.mp hs.2).2
  have hlo : Real.sqrt (value a) / 2 ≤ value (Wasm.IEEE64.sqrt a) := by
    linarith only [hl, he]
  have hhi : value (Wasm.IEEE64.sqrt a) ≤ 2 * Real.sqrt (value a) := by
    linarith only [hr, he, hroot]
  exact ⟨F64Order.positiveBits_of_finite_value_pos _ hs.1
    (lt_of_lt_of_le (by positivity) hlo), hlo, hhi⟩

#print axioms positive_range
#print axioms positive_input
#print axioms normal_relative
#print axioms mul_positive
#print axioms div_positive
#print axioms add_positive
#print axioms sqrt_positive
end Project.ProofKit.F64PositiveArithmetic
