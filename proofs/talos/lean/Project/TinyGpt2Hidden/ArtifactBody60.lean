import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence60_6_t_tail1 :
    instructionSequenceAt 24 true { bytes := artifactBytes, pos := 7802, limit := 7811 } =
      .ok (((Instr.childBody ((Cache.raw.codes[60]!.body)[6]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 7803, limit := 7811 }) := by cbv

@[cbv_eval] theorem sequence60_6_t_tail0 :
    instructionSequenceAt 25 true { bytes := artifactBytes, pos := 7800, limit := 7811 } =
      .ok (((Instr.childBody ((Cache.raw.codes[60]!.body)[6]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7803, limit := 7811 }) := by cbv

@[cbv_eval] theorem sequence60_6_e_tail1 :
    instructionSequenceAt 24 false { bytes := artifactBytes, pos := 7805, limit := 7811 } =
      .ok (((Instr.childBody ((Cache.raw.codes[60]!.body)[6]!) true).drop 1, .end), { bytes := artifactBytes, pos := 7806, limit := 7811 }) := by cbv

@[cbv_eval] theorem sequence60_6_e_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 7803, limit := 7811 } =
      .ok (((Instr.childBody ((Cache.raw.codes[60]!.body)[6]!) true).drop 0, .end), { bytes := artifactBytes, pos := 7806, limit := 7811 }) := by cbv

@[cbv_eval] theorem sequence60_tail9 :
    instructionSequenceAt 24 false { bytes := artifactBytes, pos := 7810, limit := 7811 } =
      .ok (((Cache.raw.codes[60]!.body).drop 9, .end), { bytes := artifactBytes, pos := 7811, limit := 7811 }) := by cbv

@[cbv_eval] theorem sequence60_tail8 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 7808, limit := 7811 } =
      .ok (((Cache.raw.codes[60]!.body).drop 8, .end), { bytes := artifactBytes, pos := 7811, limit := 7811 }) := by cbv

@[cbv_eval] theorem sequence60_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 7778, limit := 7811 } =
      .ok (((Cache.raw.codes[60]!.body).drop 0, .end), { bytes := artifactBytes, pos := 7811, limit := 7811 }) := by cbv

theorem code60_decoded_parts :
    code { bytes := artifactBytes, pos := 7774, limit := 16006 } = .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 7811, limit := 16006 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 7775, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 7778, limit := 7811 })
    (bodyFinish := { bytes := artifactBytes, pos := 7811, limit := 7811 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence60_tail0
  · rfl

#print axioms code60_decoded_parts
end Project.TinyGpt2Hidden.Artifact
