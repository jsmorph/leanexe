import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence46_tail92 :
    instructionSequenceAt 93 false { bytes := artifactBytes, pos := 6061, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 92, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail88 :
    instructionSequenceAt 97 false { bytes := artifactBytes, pos := 6053, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 88, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail80 :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 6037, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 80, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail72 :
    instructionSequenceAt 113 false { bytes := artifactBytes, pos := 6021, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 72, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail64 :
    instructionSequenceAt 121 false { bytes := artifactBytes, pos := 6005, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 64, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail56 :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 5989, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 56, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail48 :
    instructionSequenceAt 137 false { bytes := artifactBytes, pos := 5973, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 48, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail40 :
    instructionSequenceAt 145 false { bytes := artifactBytes, pos := 5957, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 40, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail32 :
    instructionSequenceAt 153 false { bytes := artifactBytes, pos := 5941, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 32, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail24 :
    instructionSequenceAt 161 false { bytes := artifactBytes, pos := 5925, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 24, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail16 :
    instructionSequenceAt 169 false { bytes := artifactBytes, pos := 5909, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 16, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail8 :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 5893, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 8, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

@[cbv_eval] theorem sequence46_tail0 :
    instructionSequenceAt 185 false { bytes := artifactBytes, pos := 5877, limit := 6062 } =
      .ok (((Cache.raw.codes[46]!.body).drop 0, .end), { bytes := artifactBytes, pos := 6062, limit := 6062 }) := by cbv

theorem code46_decoded_parts :
    code { bytes := artifactBytes, pos := 5872, limit := 16006 } = .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 6062, limit := 16006 }) := by
  refine code_eq_of_parts (size := 188)
    (payload := { bytes := artifactBytes, pos := 5874, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5877, limit := 6062 })
    (bodyFinish := { bytes := artifactBytes, pos := 6062, limit := 6062 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence46_tail0
  · rfl

#print axioms code46_decoded_parts
end Project.TinyGpt2Hidden.Artifact
