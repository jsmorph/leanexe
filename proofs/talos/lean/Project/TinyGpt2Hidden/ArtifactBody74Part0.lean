import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence74_1571_t_tail1 :
    instructionSequenceAt 3602 true { bytes := artifactBytes, pos := 14166, limit := 15177 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 14167, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1571_t_tail0 :
    instructionSequenceAt 3603 true { bytes := artifactBytes, pos := 14165, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 14167, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1571_e_tail1 :
    instructionSequenceAt 3602 false { bytes := artifactBytes, pos := 14170, limit := 15177 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 14171, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1571_e_tail0 :
    instructionSequenceAt 3603 false { bytes := artifactBytes, pos := 14167, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.localGet 787], .end), { bytes := artifactBytes, pos := 14171, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1602_t_tail1 :
    instructionSequenceAt 3571 true { bytes := artifactBytes, pos := 14248, limit := 15177 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 14249, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1602_t_tail0 :
    instructionSequenceAt 3572 true { bytes := artifactBytes, pos := 14247, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 14249, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1602_e_tail1 :
    instructionSequenceAt 3571 false { bytes := artifactBytes, pos := 14252, limit := 15177 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 14253, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1602_e_tail0 :
    instructionSequenceAt 3572 false { bytes := artifactBytes, pos := 14249, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.localGet 787], .end), { bytes := artifactBytes, pos := 14253, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1633_t_tail1 :
    instructionSequenceAt 3540 true { bytes := artifactBytes, pos := 14330, limit := 15177 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 14331, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1633_t_tail0 :
    instructionSequenceAt 3541 true { bytes := artifactBytes, pos := 14329, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 14331, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1633_e_tail1 :
    instructionSequenceAt 3540 false { bytes := artifactBytes, pos := 14334, limit := 15177 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 14335, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1633_e_tail0 :
    instructionSequenceAt 3541 false { bytes := artifactBytes, pos := 14331, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.localGet 787], .end), { bytes := artifactBytes, pos := 14335, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1664_t_tail1 :
    instructionSequenceAt 3509 true { bytes := artifactBytes, pos := 14412, limit := 15177 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 14413, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1664_t_tail0 :
    instructionSequenceAt 3510 true { bytes := artifactBytes, pos := 14411, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 14413, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1664_e_tail1 :
    instructionSequenceAt 3509 false { bytes := artifactBytes, pos := 14416, limit := 15177 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 14417, limit := 15177 }) := by
  cbv

@[cbv_eval] theorem sequence74_1664_e_tail0 :
    instructionSequenceAt 3510 false { bytes := artifactBytes, pos := 14413, limit := 15177 } =
      .ok (([Wasm.Binary.Instr.localGet 787], .end), { bytes := artifactBytes, pos := 14417, limit := 15177 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
