import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence76_tail12 :
    instructionSequenceAt 14 false { bytes := artifactBytes, pos := 15571, limit := 15572 } =
      .ok (((Cache.raw.codes[76]!.body).drop 12, .end), { bytes := artifactBytes, pos := 15572, limit := 15572 }) := by cbv

@[cbv_eval] theorem sequence76_tail8 :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 15563, limit := 15572 } =
      .ok (((Cache.raw.codes[76]!.body).drop 8, .end), { bytes := artifactBytes, pos := 15572, limit := 15572 }) := by cbv

@[cbv_eval] theorem sequence76_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 15546, limit := 15572 } =
      .ok (((Cache.raw.codes[76]!.body).drop 0, .end), { bytes := artifactBytes, pos := 15572, limit := 15572 }) := by cbv

theorem code76_decoded_parts :
    code { bytes := artifactBytes, pos := 15544, limit := 16006 } = .ok (Cache.raw.codes[76]!, { bytes := artifactBytes, pos := 15572, limit := 16006 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 15545, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 15546, limit := 15572 })
    (bodyFinish := { bytes := artifactBytes, pos := 15572, limit := 15572 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence76_tail0
  · rfl

#print axioms code76_decoded_parts
end Project.TinyGpt2Hidden.Artifact
