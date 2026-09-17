import Project.WGSL.GptHeadCheckpoint
import Project.TinyGpt2.NumericalLogits

namespace Project.WGSL.GptHeadCheckpoint
open Project.TinyGpt2 CodeLib.IEEE64

/-- Checkpoint weights satisfy the parent model's global input contract. -/
theorem checkpoint_weights : WeightsBounded Checkpoint.words 4 := by
  intro i hi
  have hs : i < Checkpoint.words.size := by
    rw [Checkpoint.words_size]
    exact hi
  simpa only [Affine.Bounded, getElem!_pos, hs] using Checkpoint.word_bounded i hs

/-- Error against the complete real GPT model. The three floors apply to both
computed and real normalization inputs, exactly as in the parent theorem. -/
theorem real_error {p tokens j result}
    (run : GptHead.Result p Checkpoint.words (computedHidden tokens) j result)
    (lower1 lower2 lowerFinal : ℝ)
    (hl1 : 0 < lower1) (hl2 : 0 < lower2) (hlf : 0 < lowerFinal)
    (hf1 : EmbeddingFloors Checkpoint.words tokens lower1)
    (hf2 : ResidualFloors Checkpoint.words tokens lower2)
    (hff : FinalFloors Checkpoint.words tokens lowerFinal) :
    Finite result ∧ |value result - Real.logits (parameters Checkpoint.words) tokens 3 j| ≤
      1/10000 + 16 * ErrorBudget.hidden 4 lower1 lower2 lowerFinal := by
  have he : ∀ i, |decodeRow (computedHidden tokens) i -
      Real.hidden (parameters Checkpoint.words) tokens 3 i| ≤
        ErrorBudget.hidden 4 lower1 lower2 lowerFinal := by
    intro i
    exact inputHidden_accuracy Checkpoint.words 4 lower1 lower2 lowerFinal
      (by norm_num) (by norm_num) checkpoint_weights tokens hl1 hl2 hlf hf1 hf2 hff 3 i
  exact real_error_from_hidden run _ ((abs_nonneg _).trans (he 0)) he

/-- Uniform all-input bound. This discharges every floor premise from the
positive epsilon; it does not claim the resulting worst-case bound is tight. -/
theorem real_error_uniform {p tokens j result}
    (run : GptHead.Result p Checkpoint.words (computedHidden tokens) j result) :
    Finite result ∧ |value result - Real.logits (parameters Checkpoint.words) tokens 3 j| ≤
      1/10000 + 16 * ErrorBudget.hidden 4
        (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) := by
  have hp : (0 : ℝ) < Real.sqrt (1/100000) := Real.sqrt_pos.mpr (by norm_num)
  exact real_error run _ _ _ hp hp hp (embedding_floors _ _) (residual_floors _ _) (final_floors _ _)

#print axioms real_error
#print axioms real_error_uniform
end Project.WGSL.GptHeadCheckpoint
