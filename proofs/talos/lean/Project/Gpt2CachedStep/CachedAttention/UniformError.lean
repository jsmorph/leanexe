import Project.Gpt2CachedStep.CachedAttention.SoftmaxUniform
import Project.Gpt2CachedStep.CachedAttention.ForwardError

namespace Project.Gpt2CachedStep.CachedAttention.UniformError
open Project.ProofKit CodeLib.IEEE32

noncomputable def bounds (subBound sumBound divBound mulBound addBound : Nat) : ForwardError.Bounds :=
  ⟨SoftmaxUniform.bounds subBound sumBound divBound, fun _ => mulBound, fun _ => addBound⟩

noncomputable def upper (count : Nat) (valueMagnitude : ℝ) (subBound sumBound divBound mulBound addBound : Nat) : ℝ :=
  (count : ℝ) * (F32MultiplicationBounds.epsilon mulBound +
    SoftmaxUniform.upper count subBound sumBound divBound * valueMagnitude + F32AdditionBounds.epsilon addBound)

theorem rounding_upper (cache qkv : ByteArray) (layer position i : Nat) (valueMagnitude : ℝ)
    (subBound sumBound divBound mulBound addBound : Nat)
    (h : ForwardError.Ranges cache qkv layer position i (bounds subBound sumBound divBound mulBound addBound))
    (hv : ∀ j < position + 1, |value (ForwardError.valueWords cache qkv layer position i j)| ≤ valueMagnitude) :
    ForwardError.roundingError cache qkv layer position i (bounds subBound sumBound divBound mulBound addBound) ≤
      upper (position + 1) valueMagnitude subBound sumBound divBound mulBound addBound := by
  unfold ForwardError.roundingError upper
  calc
    _ ≤ ∑ _j ∈ Finset.range (position + 1),
        (F32MultiplicationBounds.epsilon mulBound +
          SoftmaxUniform.upper (position + 1) subBound sumBound divBound * valueMagnitude +
            F32AdditionBounds.epsilon addBound) := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := SoftmaxUniform.error_upper _ _ _ subBound sumBound divBound h.softmax j (Finset.mem_range.mp hj)
      have hm := mul_le_mul hp (hv j (Finset.mem_range.mp hj)) (abs_nonneg _)
        (SoftmaxUniform.nonnegative _ _ _ _)
      exact add_le_add (add_le_add le_rfl hm) le_rfl
    _ = _ := by simp <;> ring

#print axioms rounding_upper
end Project.Gpt2CachedStep.CachedAttention.UniformError
