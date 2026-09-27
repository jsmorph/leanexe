import Project.ExpArm.TableRational
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Rational

theorem table_error (i : Nat) (hi : i < 128) :
    |value (tableScaleWord i) * (1 + value table[2*i]!) -
      Real.exp ((i : ℝ) * Real.log 2 / 128)| ≤ 1/(2 : ℝ)^104 := by
  rcases table_rational_bounds ⟨i, hi⟩ with ⟨_, _, _, hp, hl, hu⟩
  have hp' : 0 < (tableValue i : ℝ) - 1/(2 : ℝ)^104 := by
    have h : ((0 : ℚ) : ℝ) < ((tableValue i - 1/(2 : ℚ)^104 : ℚ) : ℝ) := Rat.cast_lt.mpr hp
    push_cast at h
    exact h
  have hl' : ((tableValue i : ℝ) - 1/(2 : ℝ)^104)^128 ≤ (2 : ℝ)^i := by
    have h : (((tableValue i - 1/(2 : ℚ)^104)^128 : ℚ) : ℝ) ≤ ((2^i : ℚ) : ℝ) :=
      Rat.cast_le.mpr hl
    push_cast at h
    exact h
  have hu' : (2 : ℝ)^i ≤ ((tableValue i : ℝ) + 1/(2 : ℝ)^104)^128 := by
    have h : ((2^i : ℚ) : ℝ) ≤ (((tableValue i + 1/(2 : ℚ)^104)^128 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hu
    push_cast at h
    exact h
  have he : Real.exp ((i : ℝ) * Real.log 2 / 128)^128 = (2 : ℝ)^i := by
    calc
      _ = Real.exp ((128 : ℝ) * ((i : ℝ) * Real.log 2 / 128)) :=
        (Real.exp_nat_mul _ 128).symm
      _ = Real.exp ((i : ℝ) * Real.log 2) := by congr 1; ring
      _ = (Real.exp (Real.log 2))^i := Real.exp_nat_mul _ i
      _ = (2 : ℝ)^i := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlower : (tableValue i : ℝ) - 1/(2 : ℝ)^104 ≤
      Real.exp ((i : ℝ) * Real.log 2 / 128) :=
    le_of_pow_le_pow_left₀ (by decide : (128 : Nat) ≠ 0) (Real.exp_pos _).le
      (by rw [he]; exact hl')
  have hupper : Real.exp ((i : ℝ) * Real.log 2 / 128) ≤
      (tableValue i : ℝ) + 1/(2 : ℝ)^104 :=
    le_of_pow_le_pow_left₀ (by decide : (128 : Nat) ≠ 0) (by linarith [hp'])
      (by rw [he]; exact hu')
  have h : |(tableValue i : ℝ) - Real.exp ((i : ℝ) * Real.log 2 / 128)| ≤
      1/(2 : ℝ)^104 := abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [tableValue, Rat.cast_mul, Rat.cast_add, Rat.cast_one, decode_cast] using h

#print axioms table_error
end Project.ExpArm
