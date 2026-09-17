import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence65_tail32 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 8182, limit := 8183 } =
      .ok (((Cache.raw.codes[65]!.body).drop 32, .end), { bytes := artifactBytes, pos := 8183, limit := 8183 }) := by cbv

@[cbv_eval] theorem sequence65_tail24 :
    instructionSequenceAt 41 false { bytes := artifactBytes, pos := 8166, limit := 8183 } =
      .ok (((Cache.raw.codes[65]!.body).drop 24, .end), { bytes := artifactBytes, pos := 8183, limit := 8183 }) := by cbv

@[cbv_eval] theorem sequence65_tail16 :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 8150, limit := 8183 } =
      .ok (((Cache.raw.codes[65]!.body).drop 16, .end), { bytes := artifactBytes, pos := 8183, limit := 8183 }) := by cbv

@[cbv_eval] theorem sequence65_tail8 :
    instructionSequenceAt 57 false { bytes := artifactBytes, pos := 8134, limit := 8183 } =
      .ok (((Cache.raw.codes[65]!.body).drop 8, .end), { bytes := artifactBytes, pos := 8183, limit := 8183 }) := by cbv

@[cbv_eval] theorem sequence65_tail0 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 8118, limit := 8183 } =
      .ok (((Cache.raw.codes[65]!.body).drop 0, .end), { bytes := artifactBytes, pos := 8183, limit := 8183 }) := by cbv

theorem code65_decoded_parts :
    code { bytes := artifactBytes, pos := 8114, limit := 16006 } = .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 8183, limit := 16006 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 8115, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 8118, limit := 8183 })
    (bodyFinish := { bytes := artifactBytes, pos := 8183, limit := 8183 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence65_tail0
  · rfl

#print axioms code65_decoded_parts
end Project.TinyGpt2Hidden.Artifact
