import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence51_tail29 :
    instructionSequenceAt 30 false { bytes := artifactBytes, pos := 6168, limit := 6169 } =
      .ok (((Cache.raw.codes[51]!.body).drop 29, .end), { bytes := artifactBytes, pos := 6169, limit := 6169 }) := by cbv

@[cbv_eval] theorem sequence51_tail24 :
    instructionSequenceAt 35 false { bytes := artifactBytes, pos := 6158, limit := 6169 } =
      .ok (((Cache.raw.codes[51]!.body).drop 24, .end), { bytes := artifactBytes, pos := 6169, limit := 6169 }) := by cbv

@[cbv_eval] theorem sequence51_tail16 :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 6142, limit := 6169 } =
      .ok (((Cache.raw.codes[51]!.body).drop 16, .end), { bytes := artifactBytes, pos := 6169, limit := 6169 }) := by cbv

@[cbv_eval] theorem sequence51_tail8 :
    instructionSequenceAt 51 false { bytes := artifactBytes, pos := 6126, limit := 6169 } =
      .ok (((Cache.raw.codes[51]!.body).drop 8, .end), { bytes := artifactBytes, pos := 6169, limit := 6169 }) := by cbv

@[cbv_eval] theorem sequence51_tail0 :
    instructionSequenceAt 59 false { bytes := artifactBytes, pos := 6110, limit := 6169 } =
      .ok (((Cache.raw.codes[51]!.body).drop 0, .end), { bytes := artifactBytes, pos := 6169, limit := 6169 }) := by cbv

theorem code51_decoded_parts :
    code { bytes := artifactBytes, pos := 6106, limit := 16006 } = .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 6169, limit := 16006 }) := by
  refine code_eq_of_parts (size := 62)
    (payload := { bytes := artifactBytes, pos := 6107, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 6110, limit := 6169 })
    (bodyFinish := { bytes := artifactBytes, pos := 6169, limit := 6169 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence51_tail0
  · rfl

#print axioms code51_decoded_parts
end Project.TinyGpt2Hidden.Artifact
