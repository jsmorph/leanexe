import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence11_tail18 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2334, limit := 2335 } =
      .ok (((Cache.raw.codes[11]!.body).drop 18, .end), { bytes := artifactBytes, pos := 2335, limit := 2335 }) := by cbv

@[cbv_eval] theorem sequence11_tail16 :
    instructionSequenceAt 9 false { bytes := artifactBytes, pos := 2330, limit := 2335 } =
      .ok (((Cache.raw.codes[11]!.body).drop 16, .end), { bytes := artifactBytes, pos := 2335, limit := 2335 }) := by cbv

@[cbv_eval] theorem sequence11_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 2321, limit := 2335 } =
      .ok (((Cache.raw.codes[11]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2335, limit := 2335 }) := by cbv

@[cbv_eval] theorem sequence11_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 2310, limit := 2335 } =
      .ok (((Cache.raw.codes[11]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2335, limit := 2335 }) := by cbv

theorem code11_decoded_parts :
    code { bytes := artifactBytes, pos := 2306, limit := 16006 } = .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 2335, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 2307, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2310, limit := 2335 })
    (bodyFinish := { bytes := artifactBytes, pos := 2335, limit := 2335 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence11_tail0
  · rfl

#print axioms code11_decoded_parts
end Project.TinyGpt2Hidden.Artifact
