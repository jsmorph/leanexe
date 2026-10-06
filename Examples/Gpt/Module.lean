import Examples.Gpt.Program
import Project.Compiler.Command

namespace Examples.Gpt

open Examples.Gpt in
leanexe_compile gpt := [dot, matVec, layerNorm, exp, softmax, matVec2, matMul,
  add, tanh, gelu, geluArray, mlp,
  rowMeans, rowInvStd, normalizeRows, layerNormRows,
  maskedScores, rowMax, rowSumExp, softmaxApply, softmaxRows, attention, block,
  causalMatMul, embed, matMulT, forward, linear,
  embedBlock, firstRow, stepScores, headMax, headSumExp, stepSoftmax, stepMix, writeBlock,
  appendBlock, lastHidden, layerStep, step, scores,
  Examples.Prng.splitMix, Examples.Prng.unitFloat, negInfs, insertTop,
  topKBuffer, sampleFrom, sampleTopK]

end Examples.Gpt
