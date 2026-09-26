import Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
import Project.Gpt2CachedStep.LayerNorm.RangeCertificate
import Project.Gpt2CachedStep.LayerNorm.LowerBounds
import Project.ProofKit.DyadicUpperSound

namespace Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
open Project.ProofKit
open Project.Gpt2CachedStep.LayerNorm

theorem mean_sound (p : Parameters) (ex : Nat → ℝ) (E : Nat)
    (he : ∀ i < 768, ex i ≤ DyadicUpper.value E) :
    ForwardError.meanError ex (RangeCertificate.bounds p) ≤ DyadicUpper.value (mean p E) := by
  have ha := DyadicUpper.roundoff_upper p.meanAdd 25 149
  have hd := DyadicUpper.roundoff_upper p.meanDiv 24 149
  change F32AdditionBounds.epsilon p.meanAdd ≤ _ at ha
  change F32DivisionBounds.epsilon p.meanDiv ≤ _ at hd
  have hs : (∑ i ∈ Finset.range 768, (ex i + F32AdditionBounds.epsilon p.meanAdd)) ≤
      768 * (DyadicUpper.value E + DyadicUpper.value (DyadicUpper.roundoff p.meanAdd 25 149)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range 768,
          (DyadicUpper.value E + DyadicUpper.value (DyadicUpper.roundoff p.meanAdd 25 149)) :=
        Finset.sum_le_sum fun i hi => add_le_add (he i (Finset.mem_range.mp hi)) ha
      _ = _ := by simp; ring
  simp only [mean, DyadicUpper.add_value]
  unfold ForwardError.meanError F32AverageError.error
  change F32DivisionBounds.epsilon p.meanDiv +
    (∑ i ∈ Finset.range 768, (ex i + F32AdditionBounds.epsilon p.meanAdd)) / 768 ≤ _
  exact add_le_add hd (by linarith)

theorem center_sound (p : Parameters) (ex : Nat → ℝ) (E : Nat)
    (he : ∀ i < 768, ex i ≤ DyadicUpper.value E) (i : Nat) (hi : i < 768) :
    ForwardError.centerError ex (RangeCertificate.bounds p) i ≤ DyadicUpper.value (center p E) := by
  have hs := DyadicUpper.roundoff_upper p.centerSub 25 149
  change F32AdditionBounds.epsilon p.centerSub ≤ _ at hs
  exact DyadicUpper.add_bound _ _ _ _ hs
    (DyadicUpper.add_bound _ _ _ _ (he i hi) (mean_sound p ex E he))

theorem center_nonnegative (p : Parameters) (ex : Nat → ℝ)
    (he : ∀ i < 768, 0 ≤ ex i) (i : Nat) (hi : i < 768) :
    0 ≤ ForwardError.centerError ex (RangeCertificate.bounds p) i := by
  have hMean : 0 ≤ ForwardError.meanError ex (RangeCertificate.bounds p) := by
    unfold ForwardError.meanError F32AverageError.error
    apply add_nonneg (by unfold F32DivisionBounds.epsilon; positivity)
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    exact add_nonneg (he j (Finset.mem_range.mp hj)) (by unfold F32AdditionBounds.epsilon; positivity)
  unfold ForwardError.centerError Project.Gpt2RowInvStd.Error.deltaError
  exact add_nonneg (by unfold F32AdditionBounds.epsilon; positivity) (add_nonneg (he i hi) hMean)

theorem squares_sound (input : ByteArray) (X ex : Nat → ℝ) (p : Parameters)
    (E C R : Nat) (he0 : ∀ i < 768, 0 ≤ ex i)
    (he : ∀ i < 768, ex i ≤ DyadicUpper.value E)
    (hC : ∀ i < 768, |CodeLib.IEEE32.value (Numerical.centered input i)| ≤ DyadicUpper.value C)
    (hR : ∀ i < 768, |X i - ForwardError.referenceMean X| ≤ DyadicUpper.value R) :
    ForwardError.squaresError input X ex (RangeCertificate.bounds p) ≤
      DyadicUpper.value (squares p E C R) := by
  have hm := DyadicUpper.roundoff_upper p.varianceMul 25 298
  have ha := DyadicUpper.roundoff_upper p.varianceAdd 25 149
  change F32MultiplicationBounds.epsilon p.varianceMul ≤ _ at hm
  change F32AdditionBounds.epsilon p.varianceAdd ≤ _ at ha
  let ed := ForwardError.centerError ex (RangeCertificate.bounds p)
  have hTerm (i : Nat) (hi : i < 768) :
      F32MultiplicationBounds.epsilon p.varianceMul +
        (|CodeLib.IEEE32.value (Numerical.centered input i)| * ed i + ed i * |X i - ForwardError.referenceMean X|) +
        F32AdditionBounds.epsilon p.varianceAdd ≤
      DyadicUpper.value (DyadicUpper.add (DyadicUpper.roundoff p.varianceMul 25 298)
        (DyadicUpper.add (DyadicUpper.mul (DyadicUpper.add C R) (center p E))
          (DyadicUpper.roundoff p.varianceAdd 25 149))) := by
    have hp := DyadicUpper.mul_bound
      (|CodeLib.IEEE32.value (Numerical.centered input i)| + |X i - ForwardError.referenceMean X|)
      (ed i) (DyadicUpper.add C R) (center p E) (center_nonnegative p ex he0 i hi)
      (DyadicUpper.add_bound _ _ _ _ (hC i hi) (hR i hi)) (center_sound p ex E he i hi)
    have hEq : |CodeLib.IEEE32.value (Numerical.centered input i)| * ed i +
        ed i * |X i - ForwardError.referenceMean X| =
      (|CodeLib.IEEE32.value (Numerical.centered input i)| + |X i - ForwardError.referenceMean X|) * ed i := by ring
    rw [hEq, add_assoc]
    exact DyadicUpper.add_bound _ _ _ _ hm (DyadicUpper.add_bound _ _ _ _ hp ha)
  unfold ForwardError.squaresError Project.Gpt2RowInvStd.Error.varianceError
  simp only [RangeCertificate.bounds, Project.Gpt2RowInvStd.Error.delta, Nat.zero_mul, Nat.zero_add]
  calc
    _ ≤ ∑ _i ∈ Finset.range 768, DyadicUpper.value (DyadicUpper.add (DyadicUpper.roundoff p.varianceMul 25 298)
        (DyadicUpper.add (DyadicUpper.mul (DyadicUpper.add C R) (center p E))
          (DyadicUpper.roundoff p.varianceAdd 25 149))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hTerm i (Finset.mem_range.mp hi)
    _ = _ := by simp only [squares, DyadicUpper.timesNat_value, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]

theorem root_sound (p : Parameters) (totalError : ℝ) (T : Nat)
    (ht : totalError ≤ DyadicUpper.value T) :
    Project.Gpt2RowInvStd.DenominatorError.rootError totalError (1 / 1000)
      p.varianceDiv p.epsilonAdd p.squareRoot ≤ DyadicUpper.value (rootFromSquares p T) := by
  have hs := DyadicUpper.roundoff_upper p.squareRoot 23 149
  have ha := DyadicUpper.roundoff_upper p.epsilonAdd 25 149
  have hd := DyadicUpper.roundoff_upper p.varianceDiv 24 149
  change F32SqrtBounds.epsilon p.squareRoot ≤ _ at hs
  change F32AdditionBounds.epsilon p.epsilonAdd ≤ _ at ha
  change F32DivisionBounds.epsilon p.varianceDiv ≤ _ at hd
  have hi := DyadicUpper.add_bound _ _ _ _ ha (DyadicUpper.add_bound _ _ _ _ hd
    (DyadicUpper.divNat_bound totalError T 768 (by decide) ht))
  have hc := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 1000)
  unfold Project.Gpt2RowInvStd.DenominatorError.rootError rootFromSquares
  rw [DyadicUpper.add_value, DyadicUpper.timesNat_value]
  apply add_le_add hs
  convert hc using 1 <;> ring

theorem inverse_sound (input : ByteArray) (X ex : Nat → ℝ) (p : Parameters)
    (E C R : Nat) (he0 : ∀ i < 768, 0 ≤ ex i)
    (he : ∀ i < 768, ex i ≤ DyadicUpper.value E)
    (hC : ∀ i < 768, |CodeLib.IEEE32.value (Numerical.centered input i)| ≤ DyadicUpper.value C)
    (hR : ∀ i < 768, |X i - ForwardError.referenceMean X| ≤ DyadicUpper.value R) :
    ForwardError.inverseError input X ex (RangeCertificate.bounds p) (1 / 1000) (1 / 1000) ≤
      DyadicUpper.value (inverse p E C R) := by
  have ht := squares_sound input X ex p E C R he0 he hC hR
  have hr := root_sound p _ _ ht
  have hRef := LowerBounds.reference_inverse X
  have hAbs : |ForwardError.referenceInverse X| ≤ 1000 := by rw [abs_of_nonneg hRef.1]; exact hRef.2
  have hp := (mul_le_mul_of_nonneg_left hr (abs_nonneg (ForwardError.referenceInverse X))).trans
    (mul_le_mul_of_nonneg_right hAbs (DyadicUpper.nonnegative _))
  have hc := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1000)
  have hd := DyadicUpper.roundoff_upper p.reciprocal 24 149
  change F32DivisionBounds.epsilon p.reciprocal ≤ _ at hd
  unfold ForwardError.inverseError Project.Gpt2RowInvStd.DenominatorError.inverseError inverse
  rw [DyadicUpper.add_value, DyadicUpper.timesNat_value]
  apply add_le_add hd
  convert hc using 1 <;> simp only [ForwardError.referenceInverse, RangeCertificate.bounds, root] <;> ring

theorem component_sound (weights input : ByteArray) (scaleOffset : Nat) (X ex : Nat → ℝ)
    (p : Parameters) (E C R G : Nat) (he0 : ∀ i < 768, 0 ≤ ex i)
    (he : ∀ i < 768, ex i ≤ DyadicUpper.value E)
    (hC : ∀ i < 768, |CodeLib.IEEE32.value (Numerical.centered input i)| ≤ DyadicUpper.value C)
    (hR : ∀ i < 768, |X i - ForwardError.referenceMean X| ≤ DyadicUpper.value R)
    (hG : ∀ i < 768, |CodeLib.IEEE32.value (LeanExe.Models.Gpt2.word weights (scaleOffset + i))| ≤ DyadicUpper.value G)
    (i : Nat) (hi : i < 768) :
    ForwardError.componentError weights input scaleOffset X ex (RangeCertificate.bounds p) (1 / 1000) (1 / 1000) i ≤
      DyadicUpper.value (component p E C R G) := by
  have hc := center_sound p ex E he i hi
  have hc0 := center_nonnegative p ex he0 i hi
  have hv := inverse_sound input X ex p E C R he0 he hC hR
  have hRef := LowerBounds.reference_inverse X
  have hAbs : |ForwardError.referenceInverse X| ≤ 1000 := by rw [abs_of_nonneg hRef.1]; exact hRef.2
  have hLeft := DyadicUpper.mul_bound_left _ _ _ _ (abs_nonneg _) (hC i hi) hv
  have hRight : ForwardError.centerError ex (RangeCertificate.bounds p) i * |ForwardError.referenceInverse X| ≤
      DyadicUpper.value (1000 * center p E) := by
    rw [DyadicUpper.timesNat_value]
    norm_num only [Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left hAbs hc0).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 1000))
  have hn := DyadicUpper.roundoff_upper p.normalizedMul 25 298
  have hs := DyadicUpper.roundoff_upper p.scaleMul 25 298
  have ha := DyadicUpper.roundoff_upper p.biasAdd 25 149
  change F32MultiplicationBounds.epsilon p.normalizedMul ≤ _ at hn
  change F32MultiplicationBounds.epsilon p.scaleMul ≤ _ at hs
  change F32AdditionBounds.epsilon p.biasAdd ≤ _ at ha
  have hInner := DyadicUpper.add_bound _ _ _ _ hn (DyadicUpper.add_bound _ _ _ _ hLeft hRight)
  have hGain := DyadicUpper.mul_bound _ _ _ _ (abs_nonneg _) hInner (hG i hi)
  exact DyadicUpper.add_bound _ _ _ _ ha (DyadicUpper.add_bound _ _ _ _ hs hGain)

#print axioms mean_sound
#print axioms center_sound
#print axioms squares_sound
#print axioms component_sound
end Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
