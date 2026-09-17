import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence12_tail131 :
    instructionSequenceAt 116 false { bytes := artifactBytes, pos := 2586, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 131, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail128 :
    instructionSequenceAt 119 false { bytes := artifactBytes, pos := 2580, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 128, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail120 :
    instructionSequenceAt 127 false { bytes := artifactBytes, pos := 2564, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 120, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail112 :
    instructionSequenceAt 135 false { bytes := artifactBytes, pos := 2548, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 112, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail104 :
    instructionSequenceAt 143 false { bytes := artifactBytes, pos := 2532, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 104, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail96 :
    instructionSequenceAt 151 false { bytes := artifactBytes, pos := 2516, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 96, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail88 :
    instructionSequenceAt 159 false { bytes := artifactBytes, pos := 2500, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 88, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail80 :
    instructionSequenceAt 167 false { bytes := artifactBytes, pos := 2484, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 80, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail72 :
    instructionSequenceAt 175 false { bytes := artifactBytes, pos := 2468, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 72, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail64 :
    instructionSequenceAt 183 false { bytes := artifactBytes, pos := 2452, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 64, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail56 :
    instructionSequenceAt 191 false { bytes := artifactBytes, pos := 2436, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 56, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail48 :
    instructionSequenceAt 199 false { bytes := artifactBytes, pos := 2420, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 48, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail40 :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 2407, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 40, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail32 :
    instructionSequenceAt 215 false { bytes := artifactBytes, pos := 2395, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 32, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail24 :
    instructionSequenceAt 223 false { bytes := artifactBytes, pos := 2384, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 24, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail16 :
    instructionSequenceAt 231 false { bytes := artifactBytes, pos := 2372, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 16, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail8 :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 2356, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

@[cbv_eval] theorem sequence12_tail0 :
    instructionSequenceAt 247 false { bytes := artifactBytes, pos := 2340, limit := 2587 } =
      .ok (((Cache.raw.codes[12]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2587, limit := 2587 }) := by cbv

theorem code12_decoded_parts :
    code { bytes := artifactBytes, pos := 2335, limit := 16006 } = .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 2587, limit := 16006 }) := by
  refine code_eq_of_parts (size := 250)
    (payload := { bytes := artifactBytes, pos := 2337, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2340, limit := 2587 })
    (bodyFinish := { bytes := artifactBytes, pos := 2587, limit := 2587 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence12_tail0
  · rfl

#print axioms code12_decoded_parts
end Project.TinyGpt2Hidden.Artifact
