import Project.ProofKit.F32DyadicBounds
import CodeLib.IEEE32.Multiplication

set_option exponentiation.threshold 512

namespace Project.ProofKit.F32MultiplicationBounds
open CodeLib.IEEE32

theorem mul_scaled_error (a b : UInt32) (bound : Nat)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425) (ha : Finite a) (hb : Finite b)
    (hProduct : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2 ^ bound) :
    Finite (Wasm.IEEE32.mul a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.mul a b) * (2 : Int) ^ 149 -
        Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b| ≤
          (2 ^ (bound - 25) : Nat) := by
  let n := Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b
  have hs := F32DyadicBounds.roundDyadicMagnitude149_spec
    (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b) n bound hLower hUpper hProduct
  have hmul := mul_finite_rounder a b ha hb
  rw [hmul]
  constructor
  · exact hs.1
  · have herr := hs.2.2
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

noncomputable def epsilon (bound : Nat) : ℝ := (2 : ℝ) ^ (bound - 25) / 2 ^ 298

theorem mul_real_error (a b : UInt32) (bound : Nat)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425) (ha : Finite a) (hb : Finite b)
    (hProduct : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2 ^ bound) :
    Finite (Wasm.IEEE32.mul a b) ∧
      |value (Wasm.IEEE32.mul a b) - value a * value b| ≤
        epsilon bound := by
  have hs := mul_scaled_error a b bound hLower hUpper ha hb hProduct
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.mul a b) * (2 : Int) ^ 149 -
        Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b
    have hz : |z| ≤ (2 ^ (bound - 25) : Nat) := hs.2
    have heq :
        value (Wasm.IEEE32.mul a b) - value a * value b =
          (z : ℝ) / (2 : ℝ) ^ 298 := by
      simp [value, z]
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 298)]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ 298)).2
    have hzReal : |(z : ℝ)| ≤ (2 : ℝ) ^ (bound - 25) := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤ (2 : ℝ) ^ (bound - 25) := hzReal
      _ = epsilon bound * (2 : ℝ) ^ 298 := by
        simp [epsilon]

#print axioms mul_scaled_error
#print axioms mul_real_error
end Project.ProofKit.F32MultiplicationBounds
