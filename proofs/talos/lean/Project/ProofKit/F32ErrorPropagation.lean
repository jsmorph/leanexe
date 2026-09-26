import Project.ProofKit.F32AdditionBounds
import Project.ProofKit.F32MultiplicationBounds
import Project.ProofKit.F32DivisionBounds
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul
import Project.ProofKit.F32Div
import Project.ProofKit.RealProductError
import Project.ProofKit.RealQuotientError

namespace Project.ProofKit.F32ErrorPropagation
open CodeLib.IEEE32

theorem add (a b : UInt32) (A B ea eb : ℝ) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hBound : bound ≤ 276)
    (hRange : (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.addBits a b) ∧
      |value (LeanExe.Float32.addBits a b) - (A + B)| ≤ F32AdditionBounds.epsilon bound + (ea + eb) := by
  have hArithmetic := F32AdditionBounds.add_real_error a b bound hBound ha hb hRange
  rw [← F32Add.add_eq] at hArithmetic
  have hOperands : |value a + value b - (A + B)| ≤ ea + eb := by
    rw [add_sub_add_comm]
    exact (abs_add_le _ _).trans (add_le_add hea heb)
  exact ⟨hArithmetic.1, (abs_sub_le _ _ _).trans (add_le_add hArithmetic.2 hOperands)⟩

theorem mul (a b : UInt32) (A B ea eb : ℝ) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425)
    (hRange : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2 ^ bound)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.mulBits a b) ∧
      |value (LeanExe.Float32.mulBits a b) - A * B| ≤
        F32MultiplicationBounds.epsilon bound + (|value a| * eb + ea * |B|) := by
  have hArithmetic := F32MultiplicationBounds.mul_real_error a b bound hLower hUpper ha hb hRange
  rw [← F32Mul.mul_eq] at hArithmetic
  have hOperands := RealProductError.product_error (value a) (value b) A B ea eb (|value a|) (|B|)
    hea heb le_rfl le_rfl
  exact ⟨hArithmetic.1, (abs_sub_le _ _ _).trans (add_le_add hArithmetic.2 hOperands)⟩

theorem quotient_perturbation (a b A B ea eb lower : ℝ)
    (hl : 0 < lower) (hb : lower ≤ |b|) (hB : B ≠ 0)
    (hea : |a - A| ≤ ea) (heb : |b - B| ≤ eb) :
    |a / b - A / B| ≤ (ea + |A / B| * eb) / lower := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb; linarith
  have hNum : |a / b - A / b| ≤ ea / |b| := by
    rw [← sub_div, abs_div]
    exact div_le_div_of_nonneg_right hea (abs_nonneg b)
  have hDen := RealQuotientError.denominator_error A b B eb hb0 hB heb
  have hEq : ea / |b| + |A| * eb / (|b| * |B|) = (ea + |A / B| * eb) / |b| := by
    rw [abs_div]
    field_simp
  have hCombined := (abs_sub_le (a / b) (A / b) (A / B)).trans (add_le_add hNum hDen)
  rw [hEq] at hCombined
  have hNonneg : 0 ≤ ea + |A / B| * eb := by
    have := (abs_nonneg _).trans hea
    have := (abs_nonneg _).trans heb
    positivity
  exact hCombined.trans (div_le_div_of_nonneg_left hNonneg hl hb)

theorem div (a b : UInt32) (A B ea eb lower : ℝ) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 275)
    (hNonzero : Wasm.IEEE32.scaledMagnitude b ≠ 0)
    (hRange : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude b * 2 ^ bound)
    (hl : 0 < lower) (hDen : lower ≤ |value b|) (hB : B ≠ 0)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.divBits a b) ∧
      |value (LeanExe.Float32.divBits a b) - A / B| ≤
        F32DivisionBounds.epsilon bound + (ea + |A / B| * eb) / lower := by
  have hArithmetic := F32DivisionBounds.div_real_error a b bound hLower hUpper ha hb hNonzero hRange
  rw [← F32Div.div_eq] at hArithmetic
  have hOperands := quotient_perturbation (value a) (value b) A B ea eb lower hl hDen hB hea heb
  exact ⟨hArithmetic.1, (abs_sub_le _ _ _).trans (add_le_add hArithmetic.2 hOperands)⟩

theorem compare (a b : UInt32) (reference ea eb : ℝ)
    (ha : |value a - reference| ≤ ea) (hb : |value b - reference| ≤ eb) :
    |value a - value b| ≤ ea + eb :=
  (abs_sub_le _ reference _).trans (add_le_add ha (by simpa only [abs_sub_comm] using hb))

#print axioms add
#print axioms mul
#print axioms quotient_perturbation
#print axioms div
#print axioms compare
end Project.ProofKit.F32ErrorPropagation
