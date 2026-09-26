import Project.ProofKit.F32RangeCheck
import Project.ProofKit.F32AdditionBounds
import Project.ProofKit.F32MultiplicationBounds
import Project.ProofKit.F32DivisionBounds
import Project.ProofKit.F32PairError

namespace Project.ProofKit.F32RangeCertificate
open CodeLib.IEEE32

theorem addition_sound (a b : UInt32) (bound : Nat) (h : addition a b bound = true) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.add a b) ∧
      |value (Wasm.IEEE32.add a b) - (value a + value b)| ≤ F32AdditionBounds.epsilon bound := by
  simp only [addition, Bool.and_eq_true, decide_eq_true_eq] at h
  exact F32AdditionBounds.add_real_error a b bound h.1.2 h.1.1.1 h.1.1.2 h.2

theorem subtraction_sound (a b : UInt32) (bound : Nat) (h : subtraction a b bound = true) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.sub a b) ∧
      |value (Wasm.IEEE32.sub a b) - (value a - value b)| ≤ F32AdditionBounds.epsilon bound := by
  simp only [subtraction, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa only [F32Sub.sub_eq] using F32PairError.sub_roundoff a b bound h.1.1.1 h.1.1.2 h.1.2 h.2

theorem multiplication_sound (a b : UInt32) (bound : Nat) (h : multiplication a b bound = true) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.mul a b) ∧
      |value (Wasm.IEEE32.mul a b) - value a * value b| ≤ F32MultiplicationBounds.epsilon bound := by
  simp only [multiplication, Bool.and_eq_true, decide_eq_true_eq] at h
  exact F32MultiplicationBounds.mul_real_error a b bound h.1.1.2 h.1.2 h.1.1.1.1 h.1.1.1.2 h.2

theorem division_sound (a b : UInt32) (bound : Nat) (h : division a b bound = true) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.div a b) ∧
      |value (Wasm.IEEE32.div a b) - value a / value b| ≤ F32DivisionBounds.epsilon bound := by
  simp only [division, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  exact F32DivisionBounds.div_real_error a b bound h.1.1.1.2 h.1.1.2 h.1.1.1.1.1 h.1.1.1.1.2 h.1.2 h.2

theorem squareRoot_sound (a : UInt32) (bound : Nat) (h : squareRoot a bound = true) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.sqrtBits a) ∧
      |value (LeanExe.Float32.sqrtBits a) - Real.sqrt (value a)| ≤ F32SqrtBounds.epsilon bound := by
  simp only [squareRoot, Bool.and_eq_true, decide_eq_true_eq] at h
  have hs : Wasm.IEEE32.sign a = false := by
    cases he : Wasm.IEEE32.sign a <;> simp_all
  exact F32SqrtBounds.sqrt_real_error a bound h.1.1.2 h.1.2 h.1.1.1.1 hs h.2

theorem lowerAbsolute_sound (a : UInt32) (numerator denominator : Nat)
    (h : lowerAbsolute a numerator denominator = true) :
    0 < (numerator : ℝ) / denominator ∧ (numerator : ℝ) / denominator ≤ |value a| := by
  simp only [lowerAbsolute, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd : (0 : ℝ) < denominator := by exact_mod_cast h.1.2
  have hn : (0 : ℝ) < numerator := by exact_mod_cast h.1.1
  have hr : (numerator : ℝ) * 2 ^ 149 ≤ (Wasm.IEEE32.scaledMagnitude a : ℝ) * denominator := by
    exact_mod_cast h.2
  have habs : |(Wasm.IEEE32.scaledValue a : ℝ)| = Wasm.IEEE32.scaledMagnitude a := by
    simp only [Wasm.IEEE32.scaledValue]
    split <;> simp
  refine ⟨div_pos hn hd, ?_⟩
  simp only [value, abs_div, habs, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)]
  exact (div_le_div_iff₀ hd (by positivity)).mpr hr

theorem rescaling_sound (a reduced : UInt32) (squares : Nat)
    (h : rescaling a reduced squares = true) :
    (2 : ℝ) ^ squares * value reduced = value a := by
  have hr : (2 : ℝ) ^ squares * (Wasm.IEEE32.scaledValue reduced : ℝ) = Wasm.IEEE32.scaledValue a := by
    have hi : (2 ^ squares : Int) * Wasm.IEEE32.scaledValue reduced = Wasm.IEEE32.scaledValue a := by
      simpa only [rescaling, decide_eq_true_eq] using h
    exact_mod_cast hi
  simp only [value, ← mul_div_assoc, hr]

example : addition 0x3F800000 0x3F800000 151 = true := by decide +kernel
example : addition 0x7F7FFFFF 0x7F7FFFFF 276 = false := by decide +kernel
example : division 0x3F800000 0 149 = false := by decide +kernel
example : multiplication 0x3F800000 0x3F800000 299 = true := by decide +kernel

#print axioms addition_sound
#print axioms subtraction_sound
#print axioms multiplication_sound
#print axioms division_sound
#print axioms squareRoot_sound
#print axioms lowerAbsolute_sound
#print axioms rescaling_sound
end Project.ProofKit.F32RangeCertificate
