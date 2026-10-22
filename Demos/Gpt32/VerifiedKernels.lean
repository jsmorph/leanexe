import Demos.Gpt32.Verified
import Demos.Gpt32.HostProgram
import LeanExe.WGSL.Workgroup

namespace Demos.Gpt32.Verified

open _root_.Demos.Gpt32

def kernelMap : KernelName → LeanExe.WGSL.Module
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

theorem kernelMap_workgroupSize (k : KernelName) : (kernelMap k).workgroupSize = 64 := by
  cases k
  · exact LeanExe.WGSL.Spec.module_workgroupSize embedGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize layerNormGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize linearGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize appendGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize scoresGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize headMaxGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize headSumGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize probsGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize mixGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize addGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize geluGpu.kernel.translated
  · exact LeanExe.WGSL.Spec.module_workgroupSize logitsGpu.kernel.translated

end Demos.Gpt32.Verified
