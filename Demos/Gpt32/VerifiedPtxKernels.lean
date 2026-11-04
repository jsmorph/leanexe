import Demos.Gpt32.VerifiedPtx
import Demos.Gpt32.HostProgram

namespace Demos.Gpt32.VerifiedPtx

open _root_.Demos.Gpt32

/-- The PTX kernel of each host call. -/
def kernelMap : KernelName → LeanExe.PTX.Module
  | .embed => embedKernel
  | .layerNorm => layerNormKernel
  | .linear => linearKernel
  | .append => appendKernel
  | .scores => scoresKernel
  | .headMax => headMaxKernel
  | .headSum => headSumKernel
  | .probs => probsKernel
  | .mix => mixKernel
  | .add => addKernel
  | .gelu => geluKernel
  | .logits => logitsKernel

end Demos.Gpt32.VerifiedPtx
