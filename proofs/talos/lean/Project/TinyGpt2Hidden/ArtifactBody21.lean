import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence21_tail12 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2970, limit := 2971 } =
      .ok (((Cache.raw.codes[21]!.body).drop 12, .end), { bytes := artifactBytes, pos := 2971, limit := 2971 }) := by cbv

@[cbv_eval] theorem sequence21_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 2962, limit := 2971 } =
      .ok (((Cache.raw.codes[21]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2971, limit := 2971 }) := by cbv

@[cbv_eval] theorem sequence21_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 2946, limit := 2971 } =
      .ok (((Cache.raw.codes[21]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2971, limit := 2971 }) := by cbv

theorem code21_decoded_parts :
    code { bytes := artifactBytes, pos := 2942, limit := 16006 } = .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2971, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 2943, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2946, limit := 2971 })
    (bodyFinish := { bytes := artifactBytes, pos := 2971, limit := 2971 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence21_tail0
  · rfl

#print axioms code21_decoded_parts
end Project.TinyGpt2Hidden.Artifact
