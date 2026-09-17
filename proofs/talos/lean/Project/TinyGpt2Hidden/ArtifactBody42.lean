import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence42_tail18 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5448, limit := 5449 } =
      .ok (((Cache.raw.codes[42]!.body).drop 18, .end), { bytes := artifactBytes, pos := 5449, limit := 5449 }) := by cbv

@[cbv_eval] theorem sequence42_tail16 :
    instructionSequenceAt 9 false { bytes := artifactBytes, pos := 5444, limit := 5449 } =
      .ok (((Cache.raw.codes[42]!.body).drop 16, .end), { bytes := artifactBytes, pos := 5449, limit := 5449 }) := by cbv

@[cbv_eval] theorem sequence42_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 5435, limit := 5449 } =
      .ok (((Cache.raw.codes[42]!.body).drop 8, .end), { bytes := artifactBytes, pos := 5449, limit := 5449 }) := by cbv

@[cbv_eval] theorem sequence42_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 5424, limit := 5449 } =
      .ok (((Cache.raw.codes[42]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5449, limit := 5449 }) := by cbv

theorem code42_decoded_parts :
    code { bytes := artifactBytes, pos := 5420, limit := 16006 } = .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5449, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 5421, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5424, limit := 5449 })
    (bodyFinish := { bytes := artifactBytes, pos := 5449, limit := 5449 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence42_tail0
  · rfl

#print axioms code42_decoded_parts
end Project.TinyGpt2Hidden.Artifact
