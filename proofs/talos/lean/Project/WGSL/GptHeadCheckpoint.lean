import Project.WGSL.GptHead
import Project.TinyGpt2.CheckpointHiddenBounds

namespace Project.WGSL.GptHeadCheckpoint
open Project.TinyGpt2 CodeLib.IEEE64 LeanExe.WGSL

def tokenWords (tokens : Real.Tokens) : Fin 4 → UInt64 := fun i => UInt64.ofNat (tokens i).val

def computedHidden (tokens : Real.Tokens) : Row :=
  hidden Checkpoint.words (tokenWords tokens 0) (tokenWords tokens 1)
    (tokenWords tokens 2) (tokenWords tokens 3) 3

theorem tokens_valid (tokens : Real.Tokens) (i : Fin 4) : (tokenWords tokens i).toNat < 256 := by
  simpa only [tokenWords, UInt64.toNat_ofNat_of_lt' (by omega : (tokens i).val < 2^64)] using (tokens i).isLt

theorem hidden_bounded (tokens : Real.Tokens) (i : Fin 4) :
    Affine.Bounded (rowWords (computedHidden tokens) i) 7 :=
  Checkpoint.hidden_bounded (tokenWords tokens) (tokens_valid tokens) 3 i

theorem weights_bounded (j : Fin 256) (i : Fin 4) :
    Affine.Bounded (matrixWords Checkpoint.words Layout.head 4 256 i j) 4 := by
  have hi : Layout.head+i.val*256+j.val < Checkpoint.words.size := by
    rw [Checkpoint.words_size]
    unfold Layout.head
    omega
  simpa only [Affine.Bounded, matrixWords, getElem!_pos, hi] using Checkpoint.word_bounded _ hi

theorem bias_bounded (j : Fin 256) : Affine.Bounded (GptHead.bias Checkpoint.words j) 4 := by
  have hi : Layout.headBias+j.val < Checkpoint.words.size := by
    rw [Checkpoint.words_size]
    unfold Layout.headBias
    omega
  simpa only [Affine.Bounded, GptHead.bias, getElem!_pos, hi] using Checkpoint.word_bounded _ hi

/-- Uniform head-only error for every four-byte input and every vocabulary
coordinate. The reference here uses the computed binary64 hidden row. -/
theorem numerical {p tokens j result}
    (run : GptHead.Result p Checkpoint.words (computedHidden tokens) j result) :
    Finite result ∧ |value result| ≤ 166 ∧
    |value result - (Real.matrixApply (parameters Checkpoint.words).head (decodeRow (computedHidden tokens)) j +
      (parameters Checkpoint.words).headBias j)| ≤ 1/10000 :=
  GptHead.numerical run (hidden_bounded tokens) (weights_bounded j) (bias_bounded j)

/-- The remaining full-model obligation is explicitly the hidden-state error;
no output-magnitude shortcut is substituted for this premise. -/
theorem real_error_from_hidden {p tokens j result}
    (run : GptHead.Result p Checkpoint.words (computedHidden tokens) j result)
    (error : ℝ) (he : 0 ≤ error)
    (hiddenError : ∀ i, |decodeRow (computedHidden tokens) i -
      Real.hidden (parameters Checkpoint.words) tokens 3 i| ≤ error) :
    Finite result ∧ |value result - Real.logits (parameters Checkpoint.words) tokens 3 j| ≤
      1/10000 + 16*error :=
  GptHead.perturbed run (hidden_bounded tokens) (weights_bounded j) (bias_bounded j)
    (Real.hidden (parameters Checkpoint.words) tokens 3) error he hiddenError

#print axioms numerical
#print axioms real_error_from_hidden
end Project.WGSL.GptHeadCheckpoint
