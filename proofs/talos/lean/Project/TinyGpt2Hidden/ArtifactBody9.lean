import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence9_tail23 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 2221, limit := 2222 } =
      .ok (((Cache.raw.codes[9]!.body).drop 23, .end), { bytes := artifactBytes, pos := 2222, limit := 2222 }) := by cbv

@[cbv_eval] theorem sequence9_tail16 :
    instructionSequenceAt 24 false { bytes := artifactBytes, pos := 2202, limit := 2222 } =
      .ok (((Cache.raw.codes[9]!.body).drop 16, .end), { bytes := artifactBytes, pos := 2222, limit := 2222 }) := by cbv

@[cbv_eval] theorem sequence9_tail8 :
    instructionSequenceAt 32 false { bytes := artifactBytes, pos := 2193, limit := 2222 } =
      .ok (((Cache.raw.codes[9]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2222, limit := 2222 }) := by cbv

@[cbv_eval] theorem sequence9_tail0 :
    instructionSequenceAt 40 false { bytes := artifactBytes, pos := 2182, limit := 2222 } =
      .ok (((Cache.raw.codes[9]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2222, limit := 2222 }) := by cbv

theorem code9_decoded_parts :
    code { bytes := artifactBytes, pos := 2178, limit := 16006 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 2222, limit := 16006 }) := by
  refine code_eq_of_parts (size := 43)
    (payload := { bytes := artifactBytes, pos := 2179, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2182, limit := 2222 })
    (bodyFinish := { bytes := artifactBytes, pos := 2222, limit := 2222 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence9_tail0
  · rfl

#print axioms code9_decoded_parts
end Project.TinyGpt2Hidden.Artifact
