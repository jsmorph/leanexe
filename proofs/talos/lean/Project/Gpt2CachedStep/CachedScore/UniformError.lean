import Project.Gpt2CachedStep.CachedScore.Error

namespace Project.Gpt2CachedStep.CachedScore.UniformError
open Project.ProofKit CodeLib.IEEE32

def bounds (mulBound addBound scaleBound : Nat) : Error.Bounds :=
  ⟨fun _ => mulBound, fun _ => addBound, scaleBound⟩

noncomputable def upper (queryMagnitude keyMagnitude queryError keyError : ℝ)
    (mulBound addBound scaleBound : Nat) : ℝ :=
  F32MultiplicationBounds.epsilon scaleBound +
    8 * (F32MultiplicationBounds.epsilon mulBound +
      (queryMagnitude * keyError + queryError * keyMagnitude) + F32AdditionBounds.epsilon addBound)

theorem error_upper (qkv : ByteArray) (head : Nat) (K : Nat → ℝ)
    (queryMagnitude keyMagnitude queryError keyError : ℝ) (mulBound addBound scaleBound : Nat)
    (hq : ∀ i < 64, |value (Error.query qkv head i)| ≤ queryMagnitude)
    (hk : ∀ i < 64, |K i| ≤ keyMagnitude) (heq : 0 ≤ queryError) (hek : 0 ≤ keyError) :
    Error.error qkv head K (fun _ => queryError) (fun _ => keyError) (bounds mulBound addBound scaleBound) ≤
      upper queryMagnitude keyMagnitude queryError keyError mulBound addBound scaleBound := by
  have hd : Error.dotError qkv head K (fun _ => queryError) (fun _ => keyError) (bounds mulBound addBound scaleBound) ≤
      64 * (F32MultiplicationBounds.epsilon mulBound +
        (queryMagnitude * keyError + queryError * keyMagnitude) + F32AdditionBounds.epsilon addBound) := by
    unfold Error.dotError
    calc
      _ ≤ ∑ _i ∈ Finset.range 64, (F32MultiplicationBounds.epsilon mulBound +
          (queryMagnitude * keyError + queryError * keyMagnitude) + F32AdditionBounds.epsilon addBound) := by
        apply Finset.sum_le_sum
        intro i hi
        have hqi := mul_le_mul_of_nonneg_right (hq i (Finset.mem_range.mp hi)) hek
        have hki := mul_le_mul_of_nonneg_left (hk i (Finset.mem_range.mp hi)) heq
        exact add_le_add (add_le_add le_rfl (add_le_add hqi hki)) le_rfl
      _ = _ := by simp <;> ring
  change F32MultiplicationBounds.epsilon scaleBound +
    Error.dotError qkv head K (fun _ => queryError) (fun _ => keyError) (bounds mulBound addBound scaleBound) / 8 ≤ _
  unfold upper
  linarith

#print axioms error_upper
end Project.Gpt2CachedStep.CachedScore.UniformError
