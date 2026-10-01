import Project.Gpt.Composites
import Project.Gpt.SampleVerify
import Project.Encoding.RoundTrip

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR

/-- `encode` succeeds on `gpt.module`, and its bytes decode to a module whose
exports compute the kernels exactly. -/
theorem gpt_bytes : ∃ bytes, Encoding.encode gpt.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 dotTuple ∧
      Implements m 4 matVecTuple ∧ Implements m 5 layerTuple ∧
      Implements m 6 LeanExe.Examples.Gpt.exp ∧
      Implements m 7 LeanExe.Examples.Gpt.softmax ∧
      Implements m 8 matVec2Tuple ∧ Implements m 9 matMulTuple ∧
      Implements m 10 addTuple ∧ Implements m 11 LeanExe.Examples.Gpt.tanh ∧
      Implements m 12 LeanExe.Examples.Gpt.gelu ∧
      Implements m 13 LeanExe.Examples.Gpt.geluArray ∧ Implements m 14 mlpTuple ∧
      Implements m 15 rowMeansTuple ∧ Implements m 16 rowInvStdTuple ∧
      Implements m 17 normalizeTuple ∧
      Implements m 18 layerNormRowsTuple ∧
      Implements m 19 maskedTuple ∧ Implements m 20 rowMaxTuple ∧
      Implements m 21 rowSumExpTuple ∧
      Implements m 22 softmaxApplyTuple ∧
      Implements m 23 softmaxRowsTuple ∧
      Implements m 24 attentionTuple ∧ Implements m 25 blockTuple ∧
      Implements m 26 causalMatMulTuple ∧ Implements m 27 embedTuple ∧
      Implements m 28 matMulTTuple ∧ Implements m 29 forwardTuple ∧
      Implements m 30 linearTuple ∧ Implements m 31 embedBlockTuple ∧
      Implements m 32 firstRowTuple ∧ Implements m 33 stepScoresTuple ∧
      Implements m 34 headMaxTuple ∧ Implements m 35 headSumExpTuple ∧
      Implements m 36 stepSoftmaxTuple ∧ Implements m 37 stepMixTuple ∧
      Implements m 38 writeBlockTuple ∧
      Implements m 39 appendBlockTuple ∧
      Implements m 40 lastHiddenTuple ∧ Implements m 41 layerStepTuple ∧
      Implements m 42 stepTuple ∧ Implements m 43 scoresTuple ∧
      Implements m 44 LeanExe.Examples.Prng.splitMix ∧
      Implements m 45 LeanExe.Examples.Prng.unitFloat ∧
      Implements m 46 LeanExe.Examples.Gpt.negInfs ∧
      Implements m 47 insertTopTuple ∧
      Implements m 48 topKBufferTuple ∧
      Implements m 49 sampleFromTuple ∧
      Implements m 50 sampleTopKTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip gpt.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, gpt.module, decoded, dot_implements, matVec_implements,
    layerNorm_implements, exp_implements, softmax_implements, matVec2_implements,
    matMul_implements, add_implements, tanh_pure.implements, gelu_pure.implements,
    geluArray_implements, mlp_implements, rowMeans_implements, rowInvStd_implements,
    normalizeRows_implements, layerNormRows_implements, maskedScores_implements,
    rowMax_implements, rowSumExp_implements, softmaxApply_implements, softmaxRows_implements,
    attention_implements, block_implements, causalMatMul_implements, embed_implements,
    matMulT_implements, forward_implements, linear_implements, embedBlock_implements,
    firstRow_implements, stepScores_implements, headMax_implements, headSumExp_implements,
    stepSoftmax_implements, stepMix_implements, writeBlock_implements, appendBlock_implements,
    lastHidden_implements, layerStep_implements, step_implements, scores_implements,
    splitMix_gpt.implements, unitFloat_gpt.implements, negInfs_implements, insertTop_implements,
    topKBuffer_implements, sampleFrom_implements, sampleTopK_implements⟩

end Project.Gpt
