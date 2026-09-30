import LeanExe.Examples.Gpt
import Project.Compiler.Command

namespace Project.Gpt

open LeanExe.Examples.Gpt in
leanexe_compile gpt := [dot, matVec, layerNorm, exp, softmax, matVec2, matMul,
  add, tanh, gelu, geluArray, mlp,
  rowMeans, rowInvStd, normalizeRows, layerNormRows,
  maskedScores, rowMax, rowSumExp, softmaxApply, softmaxRows, attention, block]

end Project.Gpt
