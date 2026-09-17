import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence64_12_e_3_t_tail1 :
    instructionSequenceAt 52 true { bytes := artifactBytes, pos := 8104, limit := 8114 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) true)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 8105, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_e_3_t_tail0 :
    instructionSequenceAt 53 true { bytes := artifactBytes, pos := 8102, limit := 8114 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) true)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8105, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_e_3_e_tail1 :
    instructionSequenceAt 52 false { bytes := artifactBytes, pos := 8107, limit := 8114 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) true)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 8108, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_e_3_e_tail0 :
    instructionSequenceAt 53 false { bytes := artifactBytes, pos := 8105, limit := 8114 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) true)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 8108, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_8_t_tail1 :
    instructionSequenceAt 61 true { bytes := artifactBytes, pos := 8061, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[8]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 8062, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_8_t_tail0 :
    instructionSequenceAt 62 true { bytes := artifactBytes, pos := 8059, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[8]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8062, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_8_e_tail1 :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 8064, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[8]!) true).drop 1, .end), { bytes := artifactBytes, pos := 8065, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_8_e_tail0 :
    instructionSequenceAt 62 false { bytes := artifactBytes, pos := 8062, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[8]!) true).drop 0, .end), { bytes := artifactBytes, pos := 8065, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_t_tail7 :
    instructionSequenceAt 51 true { bytes := artifactBytes, pos := 8085, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) false).drop 7, .otherwise), { bytes := artifactBytes, pos := 8086, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_t_tail0 :
    instructionSequenceAt 58 true { bytes := artifactBytes, pos := 8071, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8086, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_e_tail5 :
    instructionSequenceAt 53 false { bytes := artifactBytes, pos := 8110, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) true).drop 5, .end), { bytes := artifactBytes, pos := 8111, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_12_e_tail0 :
    instructionSequenceAt 58 false { bytes := artifactBytes, pos := 8086, limit := 8114 } =
      .ok (((Instr.childBody ((Cache.raw.codes[64]!.body)[12]!) true).drop 0, .end), { bytes := artifactBytes, pos := 8111, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_tail14 :
    instructionSequenceAt 58 false { bytes := artifactBytes, pos := 8113, limit := 8114 } =
      .ok (((Cache.raw.codes[64]!.body).drop 14, .end), { bytes := artifactBytes, pos := 8114, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_tail8 :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 8057, limit := 8114 } =
      .ok (((Cache.raw.codes[64]!.body).drop 8, .end), { bytes := artifactBytes, pos := 8114, limit := 8114 }) := by cbv

@[cbv_eval] theorem sequence64_tail0 :
    instructionSequenceAt 72 false { bytes := artifactBytes, pos := 8042, limit := 8114 } =
      .ok (((Cache.raw.codes[64]!.body).drop 0, .end), { bytes := artifactBytes, pos := 8114, limit := 8114 }) := by cbv

theorem code64_decoded_parts :
    code { bytes := artifactBytes, pos := 8038, limit := 16006 } = .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 8114, limit := 16006 }) := by
  refine code_eq_of_parts (size := 75)
    (payload := { bytes := artifactBytes, pos := 8039, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 8042, limit := 8114 })
    (bodyFinish := { bytes := artifactBytes, pos := 8114, limit := 8114 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence64_tail0
  · rfl

#print axioms code64_decoded_parts
end Project.TinyGpt2Hidden.Artifact
