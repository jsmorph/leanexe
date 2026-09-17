import Project.TinyGpt2.FloatSpec.Network
import Project.WGSL.GptHead

namespace Project.TinyGpt2.FloatSpec.Correspondence
open LeanExe.WGSL Project.WGSL

theorem row_words (x : Row) : row x = rowWords x := by
  funext i; fin_cases i <;> rfl

/-- Sequential binary32 accumulation agrees exactly, including the initial
addition to positive zero and every explicit binary64-to-binary32 conversion. -/
theorem headWord_eq (w : Array UInt64) (x : Row) (j : Fin 256) :
    GptHead.separateWord w x j = FloatSpec.headWord (parameters w) (row x) j := by
  simp [GptHead.separateWord, GptHead.kernel, GptHead.config, gemmCell, gemmAccum,
    Binary32.arithmetic, HeadNumerical.converted, GptHead.rowBuffer, GptHead.matrixBuffer,
    FloatSpec.headWord, FloatSpec.dot32, List.finRange_succ, parameters, matrix,
    row, vector4, rowWords, Nat.add_assoc]

theorem headResult_eq (w : Array UInt64) (x : Row) (j : Fin 256) :
    GptHead.separateResult w x j =
      FloatSpec.finish (FloatSpec.headWord (parameters w) (row x) j) ((parameters w).headBias j) := by
  rw [GptHead.separateResult, headWord_eq]
  rfl

theorem logits_eq (w : Array UInt64) (tokens : Tokens) (last : Fin 4) (j : Fin 256) :
    GptHead.separateResult w (Project.TinyGpt2.hidden w (tokenWord (tokens 0))
      (tokenWord (tokens 1)) (tokenWord (tokens 2)) (tokenWord (tokens 3)) (positionWord last)) j =
      FloatSpec.logits (parameters w) tokens last j := by
  rw [headResult_eq, hidden_eq]
  rfl

#print axioms headWord_eq
#print axioms logits_eq
end Project.TinyGpt2.FloatSpec.Correspondence
