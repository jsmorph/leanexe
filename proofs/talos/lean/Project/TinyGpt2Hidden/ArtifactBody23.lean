import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence23_tail18 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3028, limit := 3029 } =
      .ok (((Cache.raw.codes[23]!.body).drop 18, .end), { bytes := artifactBytes, pos := 3029, limit := 3029 }) := by cbv

@[cbv_eval] theorem sequence23_tail16 :
    instructionSequenceAt 9 false { bytes := artifactBytes, pos := 3024, limit := 3029 } =
      .ok (((Cache.raw.codes[23]!.body).drop 16, .end), { bytes := artifactBytes, pos := 3029, limit := 3029 }) := by cbv

@[cbv_eval] theorem sequence23_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 3015, limit := 3029 } =
      .ok (((Cache.raw.codes[23]!.body).drop 8, .end), { bytes := artifactBytes, pos := 3029, limit := 3029 }) := by cbv

@[cbv_eval] theorem sequence23_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 3004, limit := 3029 } =
      .ok (((Cache.raw.codes[23]!.body).drop 0, .end), { bytes := artifactBytes, pos := 3029, limit := 3029 }) := by cbv

theorem code23_decoded_parts :
    code { bytes := artifactBytes, pos := 3000, limit := 16006 } = .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 3029, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 3001, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 3004, limit := 3029 })
    (bodyFinish := { bytes := artifactBytes, pos := 3029, limit := 3029 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence23_tail0
  · rfl

#print axioms code23_decoded_parts
end Project.TinyGpt2Hidden.Artifact
