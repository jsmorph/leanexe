import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence67_tail12 :
    instructionSequenceAt 13 false { bytes := artifactBytes, pos := 8240, limit := 8241 } =
      .ok (((Cache.raw.codes[67]!.body).drop 12, .end), { bytes := artifactBytes, pos := 8241, limit := 8241 }) := by cbv

@[cbv_eval] theorem sequence67_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 8232, limit := 8241 } =
      .ok (((Cache.raw.codes[67]!.body).drop 8, .end), { bytes := artifactBytes, pos := 8241, limit := 8241 }) := by cbv

@[cbv_eval] theorem sequence67_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 8216, limit := 8241 } =
      .ok (((Cache.raw.codes[67]!.body).drop 0, .end), { bytes := artifactBytes, pos := 8241, limit := 8241 }) := by cbv

theorem code67_decoded_parts :
    code { bytes := artifactBytes, pos := 8212, limit := 16006 } = .ok (Cache.raw.codes[67]!, { bytes := artifactBytes, pos := 8241, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 8213, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 8216, limit := 8241 })
    (bodyFinish := { bytes := artifactBytes, pos := 8241, limit := 8241 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence67_tail0
  · rfl

#print axioms code67_decoded_parts
end Project.TinyGpt2Hidden.Artifact
