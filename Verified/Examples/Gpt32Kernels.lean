import Verified.Examples.Gpt32
import Examples.Gpt32.HostProgram
import LeanExe.WGSL.Workgroup

namespace Verified.Examples.Gpt32

open _root_.Examples.Gpt32

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

end Verified.Examples.Gpt32
