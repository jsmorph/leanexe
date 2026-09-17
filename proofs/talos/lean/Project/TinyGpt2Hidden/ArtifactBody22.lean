import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence22_tail12 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 2999, limit := 3000 } =
      .ok (((Cache.raw.codes[22]!.body).drop 12, .end), { bytes := artifactBytes, pos := 3000, limit := 3000 }) := by cbv

@[cbv_eval] theorem sequence22_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 2991, limit := 3000 } =
      .ok (((Cache.raw.codes[22]!.body).drop 8, .end), { bytes := artifactBytes, pos := 3000, limit := 3000 }) := by cbv

@[cbv_eval] theorem sequence22_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 2975, limit := 3000 } =
      .ok (((Cache.raw.codes[22]!.body).drop 0, .end), { bytes := artifactBytes, pos := 3000, limit := 3000 }) := by cbv

theorem code22_decoded_parts :
    code { bytes := artifactBytes, pos := 2971, limit := 16006 } = .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 3000, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 2972, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2975, limit := 3000 })
    (bodyFinish := { bytes := artifactBytes, pos := 3000, limit := 3000 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence22_tail0
  · rfl

#print axioms code22_decoded_parts
end Project.TinyGpt2Hidden.Artifact
