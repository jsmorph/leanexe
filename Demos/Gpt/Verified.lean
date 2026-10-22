import Verified.Reflect.Command
import Demos.Gpt.Program

namespace Demos.Gpt.Verified

open _root_.Demos.Gpt

set_option maxHeartbeats 1000000 in
verified_compile compiled := [dot, matVec, layerNorm, exp, softmax, matVec2, matMul, linear,
  add, tanh, gelu, geluArray, mlp, rowMeans, rowInvStd, normalizeRows, layerNormRows,
  maskedScores, rowMax, rowSumExp, softmaxApply, softmaxRows, causalMatMul, attention, block,
  embed, matMulT, forward, embedBlock, firstRow, stepScores, headMax, headSumExp, stepSoftmax,
  stepMix, writeBlock, appendBlock, lastHidden, layerStep, step, scores,
  _root_.Library.Random.SplitMix64.splitMix, _root_.Library.Random.SplitMix64.unitFloat, negInfs, insertTop,
  topKBuffer, sampleFrom, sampleTopK]

#print axioms compiled.forward.implements
#print axioms compiled.forward.trapFree
#print axioms compiled.step.implements
#print axioms compiled.step.trapFree
#print axioms compiled.sampleTopK.implements
#print axioms compiled.bytes

end Demos.Gpt.Verified
