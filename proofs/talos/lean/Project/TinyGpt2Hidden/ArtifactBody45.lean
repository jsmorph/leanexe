import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence45_tail20 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 5871, limit := 5872 } =
      .ok (((Cache.raw.codes[45]!.body).drop 20, .end), { bytes := artifactBytes, pos := 5872, limit := 5872 }) := by cbv

@[cbv_eval] theorem sequence45_tail16 :
    instructionSequenceAt 29 false { bytes := artifactBytes, pos := 5865, limit := 5872 } =
      .ok (((Cache.raw.codes[45]!.body).drop 16, .end), { bytes := artifactBytes, pos := 5872, limit := 5872 }) := by cbv

@[cbv_eval] theorem sequence45_tail8 :
    instructionSequenceAt 37 false { bytes := artifactBytes, pos := 5843, limit := 5872 } =
      .ok (((Cache.raw.codes[45]!.body).drop 8, .end), { bytes := artifactBytes, pos := 5872, limit := 5872 }) := by cbv

@[cbv_eval] theorem sequence45_tail0 :
    instructionSequenceAt 45 false { bytes := artifactBytes, pos := 5827, limit := 5872 } =
      .ok (((Cache.raw.codes[45]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5872, limit := 5872 }) := by cbv

theorem code45_decoded_parts :
    code { bytes := artifactBytes, pos := 5823, limit := 16006 } = .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 5872, limit := 16006 }) := by
  refine code_eq_of_parts (size := 48)
    (payload := { bytes := artifactBytes, pos := 5824, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5827, limit := 5872 })
    (bodyFinish := { bytes := artifactBytes, pos := 5872, limit := 5872 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence45_tail0
  · rfl

#print axioms code45_decoded_parts
end Project.TinyGpt2Hidden.Artifact
