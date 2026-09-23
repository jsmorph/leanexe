import Project.Gpt2QuantizedCached.Numerical.OperationUpper
import Project.Gpt2QuantizedCached.Numerical.ProjectionUniform
import Project.Gpt2CachedStep.CachedScore.UniformError
import Project.Gpt2CachedStep.CachedAttention.UniformError
import Project.ProofKit.DyadicUpperSound

namespace Project.Gpt2QuantizedCached.Numerical.OperationUpper
open Project.ProofKit
open DyadicUpper

theorem addError_sound (b : Nat) : F32AdditionBounds.epsilon b ≤ value (addError b) := roundoff_upper b 25 149
theorem mulError_sound (b : Nat) : F32MultiplicationBounds.epsilon b ≤ value (mulError b) := roundoff_upper b 25 298
theorem divError_sound (b : Nat) : F32DivisionBounds.epsilon b ≤ value (divError b) := roundoff_upper b 24 149

theorem times_bound (x : ℝ) (a n : Nat) (h : x ≤ value a) : (n : ℝ) * x ≤ value (n * a) := by
  rw [timesNat_value]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)

theorem projection_sound (width : Nat) (bias : Bool) (X W E A D : Nat)
    (p : ProjectionRangeCertificate.Parameters) :
    ProjectionUniform.upper width bias (value X) (value W) (value E) (value A) (value D) p ≤
      value (projection width bias X W E A D p) := by
  have he : value A + value E = value (add A E) := (add_value A E).symm
  have ht := add_bound _ _ _ _
    (add_bound _ _ _ _ (mul_upper W (add A E)) (mul_upper X D)) (mul_upper (add A E) D)
  have hg := add_bound _ _ _ _ (add_bound _ _ _ _ (mulError_sound p.quantizedOutput)
    (times_bound _ _ 1032256 (mulError_sound p.quantizedScale))) (times_bound _ _ 64 ht)
  have hsum := times_bound _ _ (width / 64) (add_bound _ _ _ _ hg (addError_sound p.quantizedAdd))
  have hr := times_bound _ _ width (add_bound _ _ _ _ (mulError_sound p.referenceMul) (addError_sound p.referenceAdd))
  have hqBias : (if bias then F32AdditionBounds.epsilon p.quantizedBias else 0) ≤
      value (if bias then addError p.quantizedBias else 0) := by
    cases bias <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact nonnegative 0
    · exact addError_sound _
  have hrBias : (if bias then F32AdditionBounds.epsilon p.referenceBias else 0) ≤
      value (if bias then addError p.referenceBias else 0) := by
    cases bias <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact nonnegative 0
    · exact addError_sound _
  unfold ProjectionUniform.upper Gpt2QuantizedGroupedRows.UniformError.upper
    Gpt2QuantizedGroupedRows.UniformError.groupUpper Gpt2QuantizedGroupedRows.UniformError.term ProjectionUniform.referenceUpper
  rw [he]
  exact add_bound _ _ _ _ (add_bound _ _ _ _ hsum hqBias) (add_bound _ _ _ _ hrBias hr)

theorem embedding_sound (D m a r : Nat) :
    F32AdditionBounds.epsilon a + (F32MultiplicationBounds.epsilon m + value D) + F32AdditionBounds.epsilon r ≤
      value (embedding D m a r) :=
  add_bound _ _ _ _ (add_bound _ _ _ _ (addError_sound a) (add_bound _ _ _ _ (mulError_sound m) le_rfl)) (addError_sound r)

theorem residual_sound (L R q r : Nat) :
    F32AdditionBounds.epsilon q + (value L + value R) + F32AdditionBounds.epsilon r ≤ value (residual L R q r) :=
  add_bound _ _ _ _ (add_bound _ _ _ _ (addError_sound q) (by rw [add_value])) (addError_sound r)

theorem gelu_sound (E : Nat) : (1 : ℝ) / 8 + 4 * value E ≤ value (gelu E) :=
  add_bound _ _ _ _ (by simpa only [Nat.cast_ofNat, Nat.cast_one] using fraction_upper 1 8 (by decide)) (times_bound _ _ 4 le_rfl)

theorem score_sound (Q K E C m a s : Nat) :
    Gpt2CachedStep.CachedScore.UniformError.upper (value Q) (value K) (value E) (value C) m a s ≤
      value (score Q K E C m a s) :=
  add_bound _ _ _ _ (mulError_sound s) (times_bound _ _ 8
    (add_bound _ _ _ _ (add_bound _ _ _ _ (mulError_sound m)
      (add_bound _ _ _ _ (mul_upper Q C) (mul_upper E K))) (addError_sound a)))

theorem softmax_sound (n s a d : Nat) :
    Gpt2CachedStep.CachedAttention.SoftmaxUniform.upper n s a d ≤ value (softmax n s a d) := by
  have h := add_bound _ _ _ _ (add_bound _ _ _ _ (divError_sound d)
    (times_bound _ _ (n + 1) (add_bound _ _ _ _ (fraction_upper 1 300 (by decide)) (addError_sound s))))
    (times_bound _ _ n (addError_sound a))
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  simpa only [Gpt2CachedStep.CachedAttention.SoftmaxUniform.upper, softmax, Nat.cast_add, Nat.cast_one] using h

theorem attentionRound_sound (n V s a d m b : Nat) :
    Gpt2CachedStep.CachedAttention.UniformError.upper n (value V) s a d m b ≤ value (attentionRound n V s a d m b) :=
  times_bound _ _ n (add_bound _ _ _ _ (add_bound _ _ _ _ (mulError_sound m)
    (mul_bound _ _ _ _ (nonnegative V) (softmax_sound n s a d) le_rfl)) (addError_sound b))

#print axioms projection_sound
#print axioms score_sound
#print axioms attentionRound_sound
end Project.Gpt2QuantizedCached.Numerical.OperationUpper
