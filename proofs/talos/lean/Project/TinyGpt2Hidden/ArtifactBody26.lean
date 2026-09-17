import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence26_tail128 :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3802, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 128, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail120 :
    instructionSequenceAt 137 false { bytes := artifactBytes, pos := 3786, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 120, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail112 :
    instructionSequenceAt 145 false { bytes := artifactBytes, pos := 3770, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 112, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail104 :
    instructionSequenceAt 153 false { bytes := artifactBytes, pos := 3754, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 104, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail96 :
    instructionSequenceAt 161 false { bytes := artifactBytes, pos := 3738, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 96, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail88 :
    instructionSequenceAt 169 false { bytes := artifactBytes, pos := 3722, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 88, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail80 :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 3706, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 80, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail72 :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 3690, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 72, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail64 :
    instructionSequenceAt 193 false { bytes := artifactBytes, pos := 3674, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 64, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail56 :
    instructionSequenceAt 201 false { bytes := artifactBytes, pos := 3658, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 56, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail48 :
    instructionSequenceAt 209 false { bytes := artifactBytes, pos := 3642, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 48, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail40 :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 3626, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 40, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail32 :
    instructionSequenceAt 225 false { bytes := artifactBytes, pos := 3610, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 32, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail24 :
    instructionSequenceAt 233 false { bytes := artifactBytes, pos := 3594, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 24, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail16 :
    instructionSequenceAt 241 false { bytes := artifactBytes, pos := 3578, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 16, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail8 :
    instructionSequenceAt 249 false { bytes := artifactBytes, pos := 3562, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 8, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

@[cbv_eval] theorem sequence26_tail0 :
    instructionSequenceAt 257 false { bytes := artifactBytes, pos := 3546, limit := 3803 } =
      .ok (((Cache.raw.codes[26]!.body).drop 0, .end), { bytes := artifactBytes, pos := 3803, limit := 3803 }) := by cbv

theorem code26_decoded_parts :
    code { bytes := artifactBytes, pos := 3541, limit := 16006 } = .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 3803, limit := 16006 }) := by
  refine code_eq_of_parts (size := 260)
    (payload := { bytes := artifactBytes, pos := 3543, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 3546, limit := 3803 })
    (bodyFinish := { bytes := artifactBytes, pos := 3803, limit := 3803 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence26_tail0
  · rfl

#print axioms code26_decoded_parts
end Project.TinyGpt2Hidden.Artifact
