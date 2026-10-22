import Demos.Gpt.Program
import LeanExe.Compiler.Command

namespace Demos.Gpt

open Demos.Gpt in
leanexe_compile gpt := [dot, matVec, layerNorm, exp, softmax, matVec2, matMul,
  add, tanh, gelu, geluArray, mlp,
  rowMeans, rowInvStd, normalizeRows, layerNormRows,
  maskedScores, rowMax, rowSumExp, softmaxApply, softmaxRows, attention, block,
  causalMatMul, embed, matMulT, forward, linear,
  embedBlock, firstRow, stepScores, headMax, headSumExp, stepSoftmax, stepMix, writeBlock,
  appendBlock, lastHidden, layerStep, step, scores,
  Library.Random.SplitMix64.splitMix, Library.Random.SplitMix64.unitFloat, negInfs, insertTop,
  topKBuffer, sampleFrom, sampleTopK]

end Demos.Gpt
