import Project.ProofKit.F32ErrorPropagation
import Project.ProofKit.F32SqrtBounds
import Project.ProofKit.F32Sub

namespace Project.ProofKit.F32PairError
open CodeLib.IEEE32

theorem sub_roundoff (a b : UInt32) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hBound : bound ≤ 276)
    (hRange : (Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.subBits a b) ∧
      |value (LeanExe.Float32.subBits a b) - (value a - value b)| ≤ F32AdditionBounds.epsilon bound := by
  have hNeg := negate_spec b hb
  have hRange' : (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue (Wasm.IEEE32.negate b)).natAbs < 2 ^ bound := by
    simpa only [hNeg.2, sub_eq_add_neg] using hRange
  have h := F32AdditionBounds.add_real_error a (Wasm.IEEE32.negate b) bound hBound ha hNeg.1 hRange'
  have hValue : value (Wasm.IEEE32.negate b) = -value b := by
    simp only [value, hNeg.2, Int.cast_neg, neg_div]
  rw [F32Sub.sub_eq]
  simpa only [Wasm.IEEE32.sub, hValue, sub_eq_add_neg] using h

theorem add (a b A B : UInt32) (ea eb : ℝ) (bound bound' : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hA : CodeLib.IEEE32.Finite A) (hB : CodeLib.IEEE32.Finite B)
    (hBound : bound ≤ 276) (hBound' : bound' ≤ 276)
    (hRange : (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound)
    (hRange' : (Wasm.IEEE32.scaledValue A + Wasm.IEEE32.scaledValue B).natAbs < 2 ^ bound')
    (hea : |value a - value A| ≤ ea) (heb : |value b - value B| ≤ eb) :
    |value (LeanExe.Float32.addBits a b) - value (LeanExe.Float32.addBits A B)| ≤
      F32AdditionBounds.epsilon bound + (ea + eb) + F32AdditionBounds.epsilon bound' := by
  have h := F32ErrorPropagation.add a b (value A) (value B) ea eb bound ha hb hBound hRange hea heb
  have h' := F32AdditionBounds.add_real_error A B bound' hBound' hA hB hRange'
  rw [← F32Add.add_eq] at h'
  exact F32ErrorPropagation.compare _ _ _ _ _ h.2 h'.2

theorem mul (a b A B : UInt32) (ea eb : ℝ) (bound bound' : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hA : CodeLib.IEEE32.Finite A) (hB : CodeLib.IEEE32.Finite B)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425)
    (hLower' : 173 ≤ bound') (hUpper' : bound' ≤ 425)
    (hRange : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2 ^ bound)
    (hRange' : Wasm.IEEE32.scaledMagnitude A * Wasm.IEEE32.scaledMagnitude B < 2 ^ bound')
    (hea : |value a - value A| ≤ ea) (heb : |value b - value B| ≤ eb) :
    |value (LeanExe.Float32.mulBits a b) - value (LeanExe.Float32.mulBits A B)| ≤
      F32MultiplicationBounds.epsilon bound + (|value a| * eb + ea * |value B|) +
        F32MultiplicationBounds.epsilon bound' := by
  have h := F32ErrorPropagation.mul a b (value A) (value B) ea eb bound ha hb hLower hUpper hRange hea heb
  have h' := F32MultiplicationBounds.mul_real_error A B bound' hLower' hUpper' hA hB hRange'
  rw [← F32Mul.mul_eq] at h'
  exact F32ErrorPropagation.compare _ _ _ _ _ h.2 h'.2

theorem sqrt_perturbation (a b error lower : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < lower)
    (hDen : lower ≤ Real.sqrt a + Real.sqrt b) (he : |a - b| ≤ error) :
    |Real.sqrt a - Real.sqrt b| ≤ error / lower := by
  have hDenPos : 0 < Real.sqrt a + Real.sqrt b := hl.trans_le hDen
  have hEq : Real.sqrt a - Real.sqrt b = (a - b) / (Real.sqrt a + Real.sqrt b) := by
    apply (eq_div_iff hDenPos.ne').mpr
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [hEq, abs_div, abs_of_pos hDenPos]
  exact (div_le_div_of_nonneg_right he hDenPos.le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans he) hl hDen)

theorem sqrt (a A : UInt32) (error lower : ℝ) (bound bound' : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hA : CodeLib.IEEE32.Finite A)
    (hs : Wasm.IEEE32.sign a = false) (hs' : Wasm.IEEE32.sign A = false)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 274)
    (hLower' : 24 ≤ bound') (hUpper' : bound' ≤ 274)
    (hRange : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ 2 ^ (2 * bound))
    (hRange' : Wasm.IEEE32.scaledMagnitude A * 2 ^ 149 ≤ 2 ^ (2 * bound'))
    (hl : 0 < lower) (hDen : lower ≤ Real.sqrt (value a) + Real.sqrt (value A))
    (he : |value a - value A| ≤ error) :
    |value (LeanExe.Float32.sqrtBits a) - value (LeanExe.Float32.sqrtBits A)| ≤
      F32SqrtBounds.epsilon bound + error / lower + F32SqrtBounds.epsilon bound' := by
  have h := F32SqrtBounds.sqrt_real_error a bound hLower hUpper ha hs hRange
  have h' := F32SqrtBounds.sqrt_real_error A bound' hLower' hUpper' hA hs' hRange'
  have nonneg (x : UInt32) (hx : Wasm.IEEE32.sign x = false) : 0 ≤ value x := by
    simp only [value, Wasm.IEEE32.scaledValue, hx, Bool.false_eq_true, ite_false]
    positivity
  have hOperands := sqrt_perturbation (value a) (value A) error lower (nonneg a hs) (nonneg A hs') hl hDen he
  have hCombined := (abs_sub_le _ _ _).trans (add_le_add h.2 hOperands)
  exact F32ErrorPropagation.compare _ _ _ _ _ hCombined h'.2

#print axioms sub_roundoff
#print axioms add
#print axioms mul
#print axioms sqrt
end Project.ProofKit.F32PairError
