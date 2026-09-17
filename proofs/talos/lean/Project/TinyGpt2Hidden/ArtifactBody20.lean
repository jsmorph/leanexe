import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence20_tail12 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2941, limit := 2942 } =
      .ok (((Cache.raw.codes[20]!.body).drop 12, .end), { bytes := artifactBytes, pos := 2942, limit := 2942 }) := by cbv

@[cbv_eval] theorem sequence20_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 2933, limit := 2942 } =
      .ok (((Cache.raw.codes[20]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2942, limit := 2942 }) := by cbv

@[cbv_eval] theorem sequence20_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 2917, limit := 2942 } =
      .ok (((Cache.raw.codes[20]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2942, limit := 2942 }) := by cbv

theorem code20_decoded_parts :
    code { bytes := artifactBytes, pos := 2913, limit := 16006 } = .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2942, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 2914, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2917, limit := 2942 })
    (bodyFinish := { bytes := artifactBytes, pos := 2942, limit := 2942 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence20_tail0
  · rfl

#print axioms code20_decoded_parts
end Project.TinyGpt2Hidden.Artifact
