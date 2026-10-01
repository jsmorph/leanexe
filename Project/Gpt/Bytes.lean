import Project.Gpt.Composites
import Project.Encoding.RoundTrip

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR

/-- `encode` succeeds on `gpt.module`, and its bytes decode to a module whose
exports compute the kernels exactly. -/
theorem gpt_bytes : ∃ bytes, Encoding.encode gpt.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 dotTuple (fun _ => 0) ∧
      Implements m 4 matVecTuple matVecNeed ∧ Implements m 5 layerTuple layerNeed ∧
      Implements m 6 LeanExe.Examples.Gpt.exp (fun _ => 0) ∧
      Implements m 7 LeanExe.Examples.Gpt.softmax softmaxNeed ∧
      Implements m 8 matVec2Tuple matVec2Need ∧ Implements m 9 matMulTuple matMulNeed ∧
      Implements m 10 addTuple addNeed ∧ Implements m 11 LeanExe.Examples.Gpt.tanh (fun _ => 0) ∧
      Implements m 12 LeanExe.Examples.Gpt.gelu (fun _ => 0) ∧
      Implements m 13 LeanExe.Examples.Gpt.geluArray geluNeed ∧ Implements m 14 mlpTuple mlpNeed ∧
      Implements m 15 rowMeansTuple rowMeansNeed ∧ Implements m 16 rowInvStdTuple rowInvStdNeed ∧
      Implements m 17 normalizeTuple normalizeNeed ∧
      Implements m 18 layerNormRowsTuple layerNormRowsNeed ∧
      Implements m 19 maskedTuple maskedNeed ∧ Implements m 20 rowMaxTuple rowMaxNeed ∧
      Implements m 21 rowSumExpTuple rowSumExpNeed ∧
      Implements m 22 softmaxApplyTuple softmaxApplyNeed ∧
      Implements m 23 softmaxRowsTuple softmaxRowsNeed ∧
      Implements m 24 attentionTuple attentionNeed ∧ Implements m 25 blockTuple blockNeed ∧
      Implements m 26 causalMatMulTuple causalMatMulNeed ∧ Implements m 27 embedTuple embedNeed ∧
      Implements m 28 matMulTTuple matMulTNeed ∧ Implements m 29 forwardTuple forwardNeed ∧
      Implements m 30 linearTuple linearNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip gpt.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, gpt.module, decoded, dot_implements, matVec_implements,
    layerNorm_implements, exp_implements, softmax_implements, matVec2_implements,
    matMul_implements, add_implements, tanh_pure.implements, gelu_pure.implements,
    geluArray_implements, mlp_implements, rowMeans_implements, rowInvStd_implements,
    normalizeRows_implements, layerNormRows_implements, maskedScores_implements,
    rowMax_implements, rowSumExp_implements, softmaxApply_implements, softmaxRows_implements,
    attention_implements, block_implements, causalMatMul_implements, embed_implements,
    matMulT_implements, forward_implements, linear_implements⟩

end Project.Gpt
