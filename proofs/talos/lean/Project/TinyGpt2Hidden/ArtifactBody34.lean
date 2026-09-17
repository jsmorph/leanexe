import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence34_tail69 :
    instructionSequenceAt 70 false { bytes := artifactBytes, pos := 4581, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 69, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail64 :
    instructionSequenceAt 75 false { bytes := artifactBytes, pos := 4571, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 64, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail56 :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 4555, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 56, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail48 :
    instructionSequenceAt 91 false { bytes := artifactBytes, pos := 4539, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 48, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail40 :
    instructionSequenceAt 99 false { bytes := artifactBytes, pos := 4523, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 40, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail32 :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 4507, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 32, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail24 :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 4491, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 24, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail16 :
    instructionSequenceAt 123 false { bytes := artifactBytes, pos := 4475, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 16, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail8 :
    instructionSequenceAt 131 false { bytes := artifactBytes, pos := 4459, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 8, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

@[cbv_eval] theorem sequence34_tail0 :
    instructionSequenceAt 139 false { bytes := artifactBytes, pos := 4443, limit := 4582 } =
      .ok (((Cache.raw.codes[34]!.body).drop 0, .end), { bytes := artifactBytes, pos := 4582, limit := 4582 }) := by cbv

theorem code34_decoded_parts :
    code { bytes := artifactBytes, pos := 4438, limit := 16006 } = .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 4582, limit := 16006 }) := by
  refine code_eq_of_parts (size := 142)
    (payload := { bytes := artifactBytes, pos := 4440, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 4443, limit := 4582 })
    (bodyFinish := { bytes := artifactBytes, pos := 4582, limit := 4582 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence34_tail0
  · rfl

#print axioms code34_decoded_parts
end Project.TinyGpt2Hidden.Artifact
