import Demos.Gpt.Program
import LeanExe.Compiler.Command

namespace Demos.Gpt

open Demos.Gpt in
leanexe_compile gpt := [Library.Numerics.LinearAlgebra.Float64.dot, Library.Numerics.LinearAlgebra.Float64.matVec, layerNorm, exp, softmax, matVec2, Library.Numerics.LinearAlgebra.Float64.matMul,
  Library.Numerics.LinearAlgebra.Float64.add, tanh, gelu, geluArray, mlp,
  rowMeans, rowInvStd, normalizeRows, layerNormRows,
  maskedScores, rowMax, rowSumExp, softmaxApply, softmaxRows, attention, block,
  causalMatMul, embed, Library.Numerics.LinearAlgebra.Float64.matMulT, forward, linear,
  embedBlock, firstRow, stepScores, headMax, headSumExp, stepSoftmax, stepMix, writeBlock,
  appendBlock, lastHidden, layerStep, step, scores,
  Library.Random.SplitMix64.splitMix, Library.Random.SplitMix64.unitFloat, negInfs, insertTop,
  topKBuffer, sampleFrom, sampleTopK]

end Demos.Gpt
