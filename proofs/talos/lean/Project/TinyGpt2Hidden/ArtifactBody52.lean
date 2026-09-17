import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence52_tail226 :
    instructionSequenceAt 227 false { bytes := artifactBytes, pos := 6626, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 226, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail224 :
    instructionSequenceAt 229 false { bytes := artifactBytes, pos := 6622, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 224, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail216 :
    instructionSequenceAt 237 false { bytes := artifactBytes, pos := 6606, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 216, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail208 :
    instructionSequenceAt 245 false { bytes := artifactBytes, pos := 6590, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 208, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail200 :
    instructionSequenceAt 253 false { bytes := artifactBytes, pos := 6574, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 200, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail192 :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 6558, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 192, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail184 :
    instructionSequenceAt 269 false { bytes := artifactBytes, pos := 6542, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 184, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail176 :
    instructionSequenceAt 277 false { bytes := artifactBytes, pos := 6526, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 176, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail168 :
    instructionSequenceAt 285 false { bytes := artifactBytes, pos := 6510, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 168, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail160 :
    instructionSequenceAt 293 false { bytes := artifactBytes, pos := 6494, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 160, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail152 :
    instructionSequenceAt 301 false { bytes := artifactBytes, pos := 6478, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 152, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail144 :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 6462, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 144, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail136 :
    instructionSequenceAt 317 false { bytes := artifactBytes, pos := 6446, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 136, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail128 :
    instructionSequenceAt 325 false { bytes := artifactBytes, pos := 6430, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 128, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail120 :
    instructionSequenceAt 333 false { bytes := artifactBytes, pos := 6414, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 120, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail112 :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 6398, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 112, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail104 :
    instructionSequenceAt 349 false { bytes := artifactBytes, pos := 6382, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 104, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail96 :
    instructionSequenceAt 357 false { bytes := artifactBytes, pos := 6366, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 96, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail88 :
    instructionSequenceAt 365 false { bytes := artifactBytes, pos := 6350, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 88, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail80 :
    instructionSequenceAt 373 false { bytes := artifactBytes, pos := 6334, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 80, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail72 :
    instructionSequenceAt 381 false { bytes := artifactBytes, pos := 6318, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 72, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail64 :
    instructionSequenceAt 389 false { bytes := artifactBytes, pos := 6302, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 64, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail56 :
    instructionSequenceAt 397 false { bytes := artifactBytes, pos := 6286, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 56, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail48 :
    instructionSequenceAt 405 false { bytes := artifactBytes, pos := 6270, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 48, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail40 :
    instructionSequenceAt 413 false { bytes := artifactBytes, pos := 6254, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 40, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail32 :
    instructionSequenceAt 421 false { bytes := artifactBytes, pos := 6238, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 32, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail24 :
    instructionSequenceAt 429 false { bytes := artifactBytes, pos := 6222, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 24, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail16 :
    instructionSequenceAt 437 false { bytes := artifactBytes, pos := 6206, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 16, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail8 :
    instructionSequenceAt 445 false { bytes := artifactBytes, pos := 6190, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 8, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

@[cbv_eval] theorem sequence52_tail0 :
    instructionSequenceAt 453 false { bytes := artifactBytes, pos := 6174, limit := 6627 } =
      .ok (((Cache.raw.codes[52]!.body).drop 0, .end), { bytes := artifactBytes, pos := 6627, limit := 6627 }) := by cbv

theorem code52_decoded_parts :
    code { bytes := artifactBytes, pos := 6169, limit := 16006 } = .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 6627, limit := 16006 }) := by
  refine code_eq_of_parts (size := 456)
    (payload := { bytes := artifactBytes, pos := 6171, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 6174, limit := 6627 })
    (bodyFinish := { bytes := artifactBytes, pos := 6627, limit := 6627 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence52_tail0
  · rfl

#print axioms code52_decoded_parts
end Project.TinyGpt2Hidden.Artifact
