import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence38_tail217 :
    instructionSequenceAt 226 false { bytes := artifactBytes, pos := 5278, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 217, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail216 :
    instructionSequenceAt 227 false { bytes := artifactBytes, pos := 5276, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 216, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail208 :
    instructionSequenceAt 235 false { bytes := artifactBytes, pos := 5258, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 208, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail200 :
    instructionSequenceAt 243 false { bytes := artifactBytes, pos := 5247, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 200, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail192 :
    instructionSequenceAt 251 false { bytes := artifactBytes, pos := 5228, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 192, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail184 :
    instructionSequenceAt 259 false { bytes := artifactBytes, pos := 5210, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 184, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail176 :
    instructionSequenceAt 267 false { bytes := artifactBytes, pos := 5199, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 176, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail168 :
    instructionSequenceAt 275 false { bytes := artifactBytes, pos := 5180, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 168, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail160 :
    instructionSequenceAt 283 false { bytes := artifactBytes, pos := 5162, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 160, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail152 :
    instructionSequenceAt 291 false { bytes := artifactBytes, pos := 5151, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 152, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail144 :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 5132, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 144, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail136 :
    instructionSequenceAt 307 false { bytes := artifactBytes, pos := 5114, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 136, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail128 :
    instructionSequenceAt 315 false { bytes := artifactBytes, pos := 5103, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 128, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail120 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 5084, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 120, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail112 :
    instructionSequenceAt 331 false { bytes := artifactBytes, pos := 5066, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 112, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail104 :
    instructionSequenceAt 339 false { bytes := artifactBytes, pos := 5055, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 104, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail96 :
    instructionSequenceAt 347 false { bytes := artifactBytes, pos := 5036, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 96, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail88 :
    instructionSequenceAt 355 false { bytes := artifactBytes, pos := 5018, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 88, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail80 :
    instructionSequenceAt 363 false { bytes := artifactBytes, pos := 5007, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 80, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail72 :
    instructionSequenceAt 371 false { bytes := artifactBytes, pos := 4988, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 72, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail64 :
    instructionSequenceAt 379 false { bytes := artifactBytes, pos := 4970, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 64, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail56 :
    instructionSequenceAt 387 false { bytes := artifactBytes, pos := 4959, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 56, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail48 :
    instructionSequenceAt 395 false { bytes := artifactBytes, pos := 4940, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 48, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail40 :
    instructionSequenceAt 403 false { bytes := artifactBytes, pos := 4922, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 40, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail32 :
    instructionSequenceAt 411 false { bytes := artifactBytes, pos := 4911, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 32, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail24 :
    instructionSequenceAt 419 false { bytes := artifactBytes, pos := 4892, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 24, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail16 :
    instructionSequenceAt 427 false { bytes := artifactBytes, pos := 4874, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 16, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail8 :
    instructionSequenceAt 435 false { bytes := artifactBytes, pos := 4863, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 8, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

@[cbv_eval] theorem sequence38_tail0 :
    instructionSequenceAt 443 false { bytes := artifactBytes, pos := 4836, limit := 5279 } =
      .ok (((Cache.raw.codes[38]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5279, limit := 5279 }) := by cbv

theorem code38_decoded_parts :
    code { bytes := artifactBytes, pos := 4831, limit := 16006 } = .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 5279, limit := 16006 }) := by
  refine code_eq_of_parts (size := 446)
    (payload := { bytes := artifactBytes, pos := 4833, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 4836, limit := 5279 })
    (bodyFinish := { bytes := artifactBytes, pos := 5279, limit := 5279 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence38_tail0
  · rfl

#print axioms code38_decoded_parts
end Project.TinyGpt2Hidden.Artifact
