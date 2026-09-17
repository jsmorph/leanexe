import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence19_tail12 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2912, limit := 2913 } =
      .ok (((Cache.raw.codes[19]!.body).drop 12, .end), { bytes := artifactBytes, pos := 2913, limit := 2913 }) := by cbv

@[cbv_eval] theorem sequence19_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 2904, limit := 2913 } =
      .ok (((Cache.raw.codes[19]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2913, limit := 2913 }) := by cbv

@[cbv_eval] theorem sequence19_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 2888, limit := 2913 } =
      .ok (((Cache.raw.codes[19]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2913, limit := 2913 }) := by cbv

theorem code19_decoded_parts :
    code { bytes := artifactBytes, pos := 2884, limit := 16006 } = .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2913, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 2885, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2888, limit := 2913 })
    (bodyFinish := { bytes := artifactBytes, pos := 2913, limit := 2913 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence19_tail0
  · rfl

#print axioms code19_decoded_parts
end Project.TinyGpt2Hidden.Artifact
