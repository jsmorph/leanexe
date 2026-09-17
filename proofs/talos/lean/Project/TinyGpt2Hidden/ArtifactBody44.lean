import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence44_tail170 :
    instructionSequenceAt 171 false { bytes := artifactBytes, pos := 5822, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 170, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail168 :
    instructionSequenceAt 173 false { bytes := artifactBytes, pos := 5818, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 168, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail160 :
    instructionSequenceAt 181 false { bytes := artifactBytes, pos := 5802, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 160, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail152 :
    instructionSequenceAt 189 false { bytes := artifactBytes, pos := 5786, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 152, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail144 :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 5770, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 144, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail136 :
    instructionSequenceAt 205 false { bytes := artifactBytes, pos := 5754, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 136, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail128 :
    instructionSequenceAt 213 false { bytes := artifactBytes, pos := 5738, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 128, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail120 :
    instructionSequenceAt 221 false { bytes := artifactBytes, pos := 5722, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 120, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail112 :
    instructionSequenceAt 229 false { bytes := artifactBytes, pos := 5706, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 112, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail104 :
    instructionSequenceAt 237 false { bytes := artifactBytes, pos := 5690, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 104, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail96 :
    instructionSequenceAt 245 false { bytes := artifactBytes, pos := 5674, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 96, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail88 :
    instructionSequenceAt 253 false { bytes := artifactBytes, pos := 5658, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 88, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail80 :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 5642, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 80, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail72 :
    instructionSequenceAt 269 false { bytes := artifactBytes, pos := 5626, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 72, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail64 :
    instructionSequenceAt 277 false { bytes := artifactBytes, pos := 5610, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 64, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail56 :
    instructionSequenceAt 285 false { bytes := artifactBytes, pos := 5594, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 56, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail48 :
    instructionSequenceAt 293 false { bytes := artifactBytes, pos := 5578, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 48, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail40 :
    instructionSequenceAt 301 false { bytes := artifactBytes, pos := 5562, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 40, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail32 :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 5546, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 32, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail24 :
    instructionSequenceAt 317 false { bytes := artifactBytes, pos := 5530, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 24, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail16 :
    instructionSequenceAt 325 false { bytes := artifactBytes, pos := 5514, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 16, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail8 :
    instructionSequenceAt 333 false { bytes := artifactBytes, pos := 5498, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 8, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

@[cbv_eval] theorem sequence44_tail0 :
    instructionSequenceAt 341 false { bytes := artifactBytes, pos := 5482, limit := 5823 } =
      .ok (((Cache.raw.codes[44]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5823, limit := 5823 }) := by cbv

theorem code44_decoded_parts :
    code { bytes := artifactBytes, pos := 5477, limit := 16006 } = .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5823, limit := 16006 }) := by
  refine code_eq_of_parts (size := 344)
    (payload := { bytes := artifactBytes, pos := 5479, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5482, limit := 5823 })
    (bodyFinish := { bytes := artifactBytes, pos := 5823, limit := 5823 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence44_tail0
  · rfl

#print axioms code44_decoded_parts
end Project.TinyGpt2Hidden.Artifact
