import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence63_36_t_tail6 :
    instructionSequenceAt 77 true { bytes := artifactBytes, pos := 8011, limit := 8038 } =
      .ok (((Instr.childBody ((Cache.raw.codes[63]!.body)[36]!) false).drop 6, .otherwise), { bytes := artifactBytes, pos := 8012, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_36_t_tail0 :
    instructionSequenceAt 83 true { bytes := artifactBytes, pos := 8003, limit := 8038 } =
      .ok (((Instr.childBody ((Cache.raw.codes[63]!.body)[36]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8012, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_36_e_tail14 :
    instructionSequenceAt 69 false { bytes := artifactBytes, pos := 8032, limit := 8038 } =
      .ok (((Instr.childBody ((Cache.raw.codes[63]!.body)[36]!) true).drop 14, .end), { bytes := artifactBytes, pos := 8033, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_36_e_tail8 :
    instructionSequenceAt 75 false { bytes := artifactBytes, pos := 8025, limit := 8038 } =
      .ok (((Instr.childBody ((Cache.raw.codes[63]!.body)[36]!) true).drop 8, .end), { bytes := artifactBytes, pos := 8033, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_36_e_tail0 :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 8012, limit := 8038 } =
      .ok (((Instr.childBody ((Cache.raw.codes[63]!.body)[36]!) true).drop 0, .end), { bytes := artifactBytes, pos := 8033, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_tail39 :
    instructionSequenceAt 82 false { bytes := artifactBytes, pos := 8037, limit := 8038 } =
      .ok (((Cache.raw.codes[63]!.body).drop 39, .end), { bytes := artifactBytes, pos := 8038, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_tail32 :
    instructionSequenceAt 89 false { bytes := artifactBytes, pos := 7985, limit := 8038 } =
      .ok (((Cache.raw.codes[63]!.body).drop 32, .end), { bytes := artifactBytes, pos := 8038, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_tail24 :
    instructionSequenceAt 97 false { bytes := artifactBytes, pos := 7965, limit := 8038 } =
      .ok (((Cache.raw.codes[63]!.body).drop 24, .end), { bytes := artifactBytes, pos := 8038, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_tail16 :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 7949, limit := 8038 } =
      .ok (((Cache.raw.codes[63]!.body).drop 16, .end), { bytes := artifactBytes, pos := 8038, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_tail8 :
    instructionSequenceAt 113 false { bytes := artifactBytes, pos := 7933, limit := 8038 } =
      .ok (((Cache.raw.codes[63]!.body).drop 8, .end), { bytes := artifactBytes, pos := 8038, limit := 8038 }) := by cbv

@[cbv_eval] theorem sequence63_tail0 :
    instructionSequenceAt 121 false { bytes := artifactBytes, pos := 7917, limit := 8038 } =
      .ok (((Cache.raw.codes[63]!.body).drop 0, .end), { bytes := artifactBytes, pos := 8038, limit := 8038 }) := by cbv

theorem code63_decoded_parts :
    code { bytes := artifactBytes, pos := 7913, limit := 16006 } = .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 8038, limit := 16006 }) := by
  refine code_eq_of_parts (size := 124)
    (payload := { bytes := artifactBytes, pos := 7914, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 7917, limit := 8038 })
    (bodyFinish := { bytes := artifactBytes, pos := 8038, limit := 8038 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence63_tail0
  · rfl

#print axioms code63_decoded_parts
end Project.TinyGpt2Hidden.Artifact
