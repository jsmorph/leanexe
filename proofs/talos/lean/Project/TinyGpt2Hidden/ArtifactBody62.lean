import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence62_tail32 :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 7912, limit := 7913 } =
      .ok (((Cache.raw.codes[62]!.body).drop 32, .end), { bytes := artifactBytes, pos := 7913, limit := 7913 }) := by cbv

@[cbv_eval] theorem sequence62_tail24 :
    instructionSequenceAt 45 false { bytes := artifactBytes, pos := 7893, limit := 7913 } =
      .ok (((Cache.raw.codes[62]!.body).drop 24, .end), { bytes := artifactBytes, pos := 7913, limit := 7913 }) := by cbv

@[cbv_eval] theorem sequence62_tail16 :
    instructionSequenceAt 53 false { bytes := artifactBytes, pos := 7882, limit := 7913 } =
      .ok (((Cache.raw.codes[62]!.body).drop 16, .end), { bytes := artifactBytes, pos := 7913, limit := 7913 }) := by cbv

@[cbv_eval] theorem sequence62_tail8 :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 7856, limit := 7913 } =
      .ok (((Cache.raw.codes[62]!.body).drop 8, .end), { bytes := artifactBytes, pos := 7913, limit := 7913 }) := by cbv

@[cbv_eval] theorem sequence62_tail0 :
    instructionSequenceAt 69 false { bytes := artifactBytes, pos := 7844, limit := 7913 } =
      .ok (((Cache.raw.codes[62]!.body).drop 0, .end), { bytes := artifactBytes, pos := 7913, limit := 7913 }) := by cbv

theorem code62_decoded_parts :
    code { bytes := artifactBytes, pos := 7840, limit := 16006 } = .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 7913, limit := 16006 }) := by
  refine code_eq_of_parts (size := 72)
    (payload := { bytes := artifactBytes, pos := 7841, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 7844, limit := 7913 })
    (bodyFinish := { bytes := artifactBytes, pos := 7913, limit := 7913 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence62_tail0
  · rfl

#print axioms code62_decoded_parts
end Project.TinyGpt2Hidden.Artifact
