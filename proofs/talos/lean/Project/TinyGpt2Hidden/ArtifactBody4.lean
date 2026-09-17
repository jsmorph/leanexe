import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence4_tail32 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 1157, limit := 1158 } =
      .ok (((Cache.raw.codes[4]!.body).drop 32, .end), { bytes := artifactBytes, pos := 1158, limit := 1158 }) := by cbv

@[cbv_eval] theorem sequence4_tail24 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 1144, limit := 1158 } =
      .ok (((Cache.raw.codes[4]!.body).drop 24, .end), { bytes := artifactBytes, pos := 1158, limit := 1158 }) := by cbv

@[cbv_eval] theorem sequence4_tail16 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 1132, limit := 1158 } =
      .ok (((Cache.raw.codes[4]!.body).drop 16, .end), { bytes := artifactBytes, pos := 1158, limit := 1158 }) := by cbv

@[cbv_eval] theorem sequence4_tail8 :
    instructionSequenceAt 41 false { bytes := artifactBytes, pos := 1121, limit := 1158 } =
      .ok (((Cache.raw.codes[4]!.body).drop 8, .end), { bytes := artifactBytes, pos := 1158, limit := 1158 }) := by cbv

@[cbv_eval] theorem sequence4_tail0 :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 1109, limit := 1158 } =
      .ok (((Cache.raw.codes[4]!.body).drop 0, .end), { bytes := artifactBytes, pos := 1158, limit := 1158 }) := by cbv

theorem code4_decoded_parts :
    code { bytes := artifactBytes, pos := 1105, limit := 16006 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 1158, limit := 16006 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 1106, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 1109, limit := 1158 })
    (bodyFinish := { bytes := artifactBytes, pos := 1158, limit := 1158 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence4_tail0
  · rfl

#print axioms code4_decoded_parts
end Project.TinyGpt2Hidden.Artifact
