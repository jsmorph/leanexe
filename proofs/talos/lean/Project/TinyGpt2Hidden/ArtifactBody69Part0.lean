import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence69_79_e_5_t_tail1 :
    instructionSequenceAt 877 true { bytes := artifactBytes, pos := 8581, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8582, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_79_e_5_t_tail0 :
    instructionSequenceAt 878 true { bytes := artifactBytes, pos := 8580, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8582, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_79_e_5_e_tail3 :
    instructionSequenceAt 875 false { bytes := artifactBytes, pos := 8587, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8588, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_79_e_5_e_tail0 :
    instructionSequenceAt 878 false { bytes := artifactBytes, pos := 8582, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul], .end), { bytes := artifactBytes, pos := 8588, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_e_5_t_tail1 :
    instructionSequenceAt 839 true { bytes := artifactBytes, pos := 8704, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8705, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_e_5_t_tail0 :
    instructionSequenceAt 840 true { bytes := artifactBytes, pos := 8703, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8705, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_e_5_e_tail3 :
    instructionSequenceAt 837 false { bytes := artifactBytes, pos := 8710, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8711, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_117_e_5_e_tail0 :
    instructionSequenceAt 840 false { bytes := artifactBytes, pos := 8705, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul], .end), { bytes := artifactBytes, pos := 8711, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_e_5_t_tail1 :
    instructionSequenceAt 801 true { bytes := artifactBytes, pos := 8827, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8828, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_e_5_t_tail0 :
    instructionSequenceAt 802 true { bytes := artifactBytes, pos := 8826, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8828, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_e_5_e_tail3 :
    instructionSequenceAt 799 false { bytes := artifactBytes, pos := 8833, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8834, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_155_e_5_e_tail0 :
    instructionSequenceAt 802 false { bytes := artifactBytes, pos := 8828, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul], .end), { bytes := artifactBytes, pos := 8834, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_e_5_t_tail1 :
    instructionSequenceAt 763 true { bytes := artifactBytes, pos := 8950, limit := 9325 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 8951, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_e_5_t_tail0 :
    instructionSequenceAt 764 true { bytes := artifactBytes, pos := 8949, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 8951, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_e_5_e_tail3 :
    instructionSequenceAt 761 false { bytes := artifactBytes, pos := 8956, limit := 9325 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 8957, limit := 9325 }) := by
  cbv

@[cbv_eval] theorem sequence69_193_e_5_e_tail0 :
    instructionSequenceAt 764 false { bytes := artifactBytes, pos := 8951, limit := 9325 } =
      .ok (([Wasm.Binary.Instr.localGet 39, Wasm.Binary.Instr.localGet 40, Wasm.Binary.Instr.i64Mul], .end), { bytes := artifactBytes, pos := 8957, limit := 9325 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
