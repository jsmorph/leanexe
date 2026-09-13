import Project.ProofKit.F64AddBounds
import Project.ProofKit.F64MulBounds
import Project.ProofKit.F64DivBounds

namespace Project.ProofKit.F64ArithmeticBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem epsilon_pos : 0 < arithmeticEpsilon := by norm_num [arithmeticEpsilon]
theorem epsilon_small : arithmeticEpsilon < 1 / 100 := by norm_num [arithmeticEpsilon]

theorem mixed_budget (x bound : ℝ) (hbound : 1 ≤ bound) (hx : x ≤ bound) :
    unitRoundoff64 * x + multiplicationUnderflowEpsilon ≤ arithmeticEpsilon * bound := by
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have he : multiplicationUnderflowEpsilon ≤ unitRoundoff64 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64]
  have heq : arithmeticEpsilon = 2 * unitRoundoff64 := by
    norm_num [arithmeticEpsilon, unitRoundoff64]
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hx hu, mul_le_mul_of_nonneg_left hbound hu]

theorem magnitude_of_error (rounded exactValue error bound : ℝ)
    (herr : |rounded - exactValue| ≤ error) (hbound : |exactValue| ≤ bound) :
    |rounded| ≤ bound + error := by
  have ht := abs_add_le (rounded - exactValue) exactValue
  rw [sub_add_cancel] at ht
  linarith

theorem mul_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (bound : ℝ) (hbound : 1 ≤ bound) (hmax : bound < (2 : ℝ)^1022)
    (hp : |value a * value b| ≤ bound) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ arithmeticEpsilon * bound := by
  have hs := F64MulBounds.mul_real_mixed a b ha hb (hp.trans_lt hmax)
  exact ⟨hs.1, hs.2.trans (mixed_budget _ _ hbound hp)⟩

theorem div_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (bound : ℝ) (hbound : 1 ≤ bound) (hmax : bound < (2 : ℝ)^1022)
    (hq : |value a / value b| ≤ bound) :
    Finite (Wasm.IEEE64.div a b) ∧
    |value (Wasm.IEEE64.div a b) - value a / value b| ≤ arithmeticEpsilon * bound := by
  have hs := F64DivBounds.div_real_mixed a b ha hb hb0 (hq.trans_lt hmax)
  exact ⟨hs.1, hs.2.trans (mixed_budget _ _ hbound hq)⟩

theorem add_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (bound : ℝ) (hbound : 1 ≤ bound) (hmax : bound < (2 : ℝ)^1023)
    (hsum : |value a + value b| ≤ bound) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ arithmeticEpsilon * bound := by
  have hs := F64AddBounds.add_real_relative a b ha hb (hsum.trans_lt hmax)
  have he : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  exact ⟨hs.1, hs.2.trans ((le_add_of_nonneg_right he).trans (mixed_budget _ _ hbound hsum))⟩

theorem sub_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (bound : ℝ) (hbound : 1 ≤ bound) (hmax : bound < (2 : ℝ)^1023)
    (hsub : |value a - value b| ≤ bound) :
    Finite (Wasm.IEEE64.sub a b) ∧
    |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ arithmeticEpsilon * bound := by
  have hs := F64AddBounds.sub_real_relative a b ha hb (hsub.trans_lt hmax)
  have he : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  exact ⟨hs.1, hs.2.trans ((le_add_of_nonneg_right he).trans (mixed_budget _ _ hbound hsub))⟩

#print axioms mul_error
#print axioms div_error
#print axioms add_error
#print axioms sub_error
end Project.ProofKit.F64ArithmeticBounds
