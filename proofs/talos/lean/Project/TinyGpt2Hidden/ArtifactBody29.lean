import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence29_tail152 :
    instructionSequenceAt 153 false { bytes := artifactBytes, pos := 4298, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 152, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail144 :
    instructionSequenceAt 161 false { bytes := artifactBytes, pos := 4282, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 144, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail136 :
    instructionSequenceAt 169 false { bytes := artifactBytes, pos := 4266, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 136, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail128 :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 4250, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 128, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail120 :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 4234, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 120, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail112 :
    instructionSequenceAt 193 false { bytes := artifactBytes, pos := 4218, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 112, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail104 :
    instructionSequenceAt 201 false { bytes := artifactBytes, pos := 4202, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 104, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail96 :
    instructionSequenceAt 209 false { bytes := artifactBytes, pos := 4186, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 96, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail88 :
    instructionSequenceAt 217 false { bytes := artifactBytes, pos := 4170, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 88, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail80 :
    instructionSequenceAt 225 false { bytes := artifactBytes, pos := 4154, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 80, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail72 :
    instructionSequenceAt 233 false { bytes := artifactBytes, pos := 4138, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 72, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail64 :
    instructionSequenceAt 241 false { bytes := artifactBytes, pos := 4122, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 64, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail56 :
    instructionSequenceAt 249 false { bytes := artifactBytes, pos := 4106, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 56, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail48 :
    instructionSequenceAt 257 false { bytes := artifactBytes, pos := 4090, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 48, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail40 :
    instructionSequenceAt 265 false { bytes := artifactBytes, pos := 4074, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 40, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail32 :
    instructionSequenceAt 273 false { bytes := artifactBytes, pos := 4058, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 32, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail24 :
    instructionSequenceAt 281 false { bytes := artifactBytes, pos := 4042, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 24, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail16 :
    instructionSequenceAt 289 false { bytes := artifactBytes, pos := 4026, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 16, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail8 :
    instructionSequenceAt 297 false { bytes := artifactBytes, pos := 4010, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 8, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

@[cbv_eval] theorem sequence29_tail0 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 3994, limit := 4299 } =
      .ok (((Cache.raw.codes[29]!.body).drop 0, .end), { bytes := artifactBytes, pos := 4299, limit := 4299 }) := by cbv

theorem code29_decoded_parts :
    code { bytes := artifactBytes, pos := 3989, limit := 16006 } = .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 4299, limit := 16006 }) := by
  refine code_eq_of_parts (size := 308)
    (payload := { bytes := artifactBytes, pos := 3991, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 3994, limit := 4299 })
    (bodyFinish := { bytes := artifactBytes, pos := 4299, limit := 4299 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence29_tail0
  · rfl

#print axioms code29_decoded_parts
end Project.TinyGpt2Hidden.Artifact
