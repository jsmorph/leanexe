import Project.Gpt2CachedStep.CachedAttention.SoftmaxError
import Project.Gpt2CachedStep.ExpNeg.UniformError

namespace Project.Gpt2CachedStep.CachedAttention.SoftmaxUniform
open Project.ProofKit CodeLib.IEEE32

noncomputable def bounds (subBound sumBound divBound : Nat) : SoftmaxError.Bounds :=
  ⟨fun _ => subBound, fun _ => sumBound, fun _ => divBound,
    fun _ _ => 299, fun _ _ => 151, fun _ _ => 299, 1⟩

noncomputable def upper (count subBound sumBound divBound : Nat) : ℝ :=
  F32DivisionBounds.epsilon divBound +
    ((count + 1 : Nat) : ℝ) * (1 / 300 + F32AdditionBounds.epsilon subBound) +
    (count : ℝ) * F32AdditionBounds.epsilon sumBound

theorem nonnegative (count subBound sumBound divBound : Nat) : 0 ≤ upper count subBound sumBound divBound := by
  unfold upper F32DivisionBounds.epsilon F32AdditionBounds.epsilon
  positivity

theorem exp_upper (scores : Nat → UInt32) (maximum : UInt32) (count subBound sumBound divBound : Nat)
    (h : SoftmaxError.Ranges scores maximum (bounds subBound sumBound divBound) count) (i : Nat) (hi : i < count) :
    SoftmaxError.expError scores maximum (bounds subBound sumBound divBound) i ≤
      1 / 300 + F32AdditionBounds.epsilon subBound := by
  have he := ExpNeg.UniformError.error_upper (SoftmaxError.shifted scores maximum i)
    (h.shiftedNonpositive i hi) (h.expRanges i hi)
  exact add_le_add he le_rfl

theorem sum_upper (scores : Nat → UInt32) (maximum : UInt32) (count subBound sumBound divBound : Nat)
    (h : SoftmaxError.Ranges scores maximum (bounds subBound sumBound divBound) count) :
    SoftmaxError.sumError scores maximum (bounds subBound sumBound divBound) count ≤
      (count : ℝ) * (1 / 300 + F32AdditionBounds.epsilon subBound + F32AdditionBounds.epsilon sumBound) := by
  unfold SoftmaxError.sumError
  calc
    _ ≤ ∑ _i ∈ Finset.range count,
        (1 / 300 + F32AdditionBounds.epsilon subBound + F32AdditionBounds.epsilon sumBound) := by
      apply Finset.sum_le_sum
      intro i hi
      exact add_le_add (exp_upper scores maximum count subBound sumBound divBound h i (Finset.mem_range.mp hi)) le_rfl
    _ = _ := by simp <;> ring

theorem reference_ratio (scores : Nat → UInt32) (maximum : UInt32) (count i : Nat) (hi : i < count) :
    |SoftmaxError.reference scores maximum i / (∑ j ∈ Finset.range count, SoftmaxError.reference scores maximum j)| ≤ 1 := by
  have hp := SoftmaxError.reference_sum_positive scores maximum count (by omega)
  have hn : 0 ≤ SoftmaxError.reference scores maximum i := (Real.exp_pos _).le
  rw [abs_of_nonneg (div_nonneg hn hp.le)]
  apply (div_le_one hp).mpr
  apply Finset.single_le_sum _ (Finset.mem_range.mpr hi)
  intro j _
  exact (Real.exp_pos _).le

theorem error_upper (scores : Nat → UInt32) (maximum : UInt32) (count subBound sumBound divBound : Nat)
    (h : SoftmaxError.Ranges scores maximum (bounds subBound sumBound divBound) count) (i : Nat) (hi : i < count) :
    SoftmaxError.error scores maximum (bounds subBound sumBound divBound) count i ≤
      upper count subBound sumBound divBound := by
  have he := exp_upper scores maximum count subBound sumBound divBound h i hi
  have hs := sum_upper scores maximum count subBound sumBound divBound h
  have hr := reference_ratio scores maximum count i hi
  have hm := mul_le_mul hs hr (abs_nonneg _) (by unfold F32AdditionBounds.epsilon; positivity)
  rw [mul_one] at hm
  change F32DivisionBounds.epsilon divBound +
    (SoftmaxError.expError scores maximum (bounds subBound sumBound divBound) i +
      |SoftmaxError.reference scores maximum i / (∑ j ∈ Finset.range count, SoftmaxError.reference scores maximum j)| *
        SoftmaxError.sumError scores maximum (bounds subBound sumBound divBound) count) / 1 ≤ _
  simp only [div_one, upper, Nat.cast_add, Nat.cast_one]
  nlinarith

#print axioms error_upper
end Project.Gpt2CachedStep.CachedAttention.SoftmaxUniform
