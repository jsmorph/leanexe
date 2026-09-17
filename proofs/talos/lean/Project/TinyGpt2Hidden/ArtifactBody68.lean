import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence68_tail56 :
    instructionSequenceAt 53 false { bytes := artifactBytes, pos := 8353, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 56, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail48 :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 8340, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 48, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail40 :
    instructionSequenceAt 69 false { bytes := artifactBytes, pos := 8324, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 40, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail32 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 8308, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 32, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail24 :
    instructionSequenceAt 85 false { bytes := artifactBytes, pos := 8293, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 24, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail16 :
    instructionSequenceAt 93 false { bytes := artifactBytes, pos := 8277, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 16, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail8 :
    instructionSequenceAt 101 false { bytes := artifactBytes, pos := 8261, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 8, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

@[cbv_eval] theorem sequence68_tail0 :
    instructionSequenceAt 109 false { bytes := artifactBytes, pos := 8245, limit := 8354 } =
      .ok (((Cache.raw.codes[68]!.body).drop 0, .end), { bytes := artifactBytes, pos := 8354, limit := 8354 }) := by cbv

theorem code68_decoded_parts :
    code { bytes := artifactBytes, pos := 8241, limit := 16006 } = .ok (Cache.raw.codes[68]!, { bytes := artifactBytes, pos := 8354, limit := 16006 }) := by
  refine code_eq_of_parts (size := 112)
    (payload := { bytes := artifactBytes, pos := 8242, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 8245, limit := 8354 })
    (bodyFinish := { bytes := artifactBytes, pos := 8354, limit := 8354 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence68_tail0
  · rfl

#print axioms code68_decoded_parts
end Project.TinyGpt2Hidden.Artifact
