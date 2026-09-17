import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence24_tail32 :
    instructionSequenceAt 29 false { bytes := artifactBytes, pos := 3093, limit := 3094 } =
      .ok (((Cache.raw.codes[24]!.body).drop 32, .end), { bytes := artifactBytes, pos := 3094, limit := 3094 }) := by cbv

@[cbv_eval] theorem sequence24_tail24 :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 3080, limit := 3094 } =
      .ok (((Cache.raw.codes[24]!.body).drop 24, .end), { bytes := artifactBytes, pos := 3094, limit := 3094 }) := by cbv

@[cbv_eval] theorem sequence24_tail16 :
    instructionSequenceAt 45 false { bytes := artifactBytes, pos := 3064, limit := 3094 } =
      .ok (((Cache.raw.codes[24]!.body).drop 16, .end), { bytes := artifactBytes, pos := 3094, limit := 3094 }) := by cbv

@[cbv_eval] theorem sequence24_tail8 :
    instructionSequenceAt 53 false { bytes := artifactBytes, pos := 3049, limit := 3094 } =
      .ok (((Cache.raw.codes[24]!.body).drop 8, .end), { bytes := artifactBytes, pos := 3094, limit := 3094 }) := by cbv

@[cbv_eval] theorem sequence24_tail0 :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 3033, limit := 3094 } =
      .ok (((Cache.raw.codes[24]!.body).drop 0, .end), { bytes := artifactBytes, pos := 3094, limit := 3094 }) := by cbv

theorem code24_decoded_parts :
    code { bytes := artifactBytes, pos := 3029, limit := 16006 } = .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 3094, limit := 16006 }) := by
  refine code_eq_of_parts (size := 64)
    (payload := { bytes := artifactBytes, pos := 3030, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 3033, limit := 3094 })
    (bodyFinish := { bytes := artifactBytes, pos := 3094, limit := 3094 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence24_tail0
  · rfl

#print axioms code24_decoded_parts
end Project.TinyGpt2Hidden.Artifact
