import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence17_36_t_tail1 :
    instructionSequenceAt 197 true { bytes := artifactBytes, pos := 2709, limit := 2872 } =
      .ok (((Instr.childBody ((Cache.raw.codes[17]!.body)[36]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2710, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_36_t_tail0 :
    instructionSequenceAt 198 true { bytes := artifactBytes, pos := 2708, limit := 2872 } =
      .ok (((Instr.childBody ((Cache.raw.codes[17]!.body)[36]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2710, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_36_e_tail1 :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 2712, limit := 2872 } =
      .ok (((Instr.childBody ((Cache.raw.codes[17]!.body)[36]!) true).drop 1, .end), { bytes := artifactBytes, pos := 2713, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_36_e_tail0 :
    instructionSequenceAt 198 false { bytes := artifactBytes, pos := 2710, limit := 2872 } =
      .ok (((Instr.childBody ((Cache.raw.codes[17]!.body)[36]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2713, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail116 :
    instructionSequenceAt 120 false { bytes := artifactBytes, pos := 2871, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 116, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail112 :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 2863, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 112, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail104 :
    instructionSequenceAt 132 false { bytes := artifactBytes, pos := 2847, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 104, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail96 :
    instructionSequenceAt 140 false { bytes := artifactBytes, pos := 2831, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 96, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail88 :
    instructionSequenceAt 148 false { bytes := artifactBytes, pos := 2815, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 88, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail80 :
    instructionSequenceAt 156 false { bytes := artifactBytes, pos := 2799, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 80, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail72 :
    instructionSequenceAt 164 false { bytes := artifactBytes, pos := 2783, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 72, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail64 :
    instructionSequenceAt 172 false { bytes := artifactBytes, pos := 2767, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 64, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail56 :
    instructionSequenceAt 180 false { bytes := artifactBytes, pos := 2751, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 56, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail48 :
    instructionSequenceAt 188 false { bytes := artifactBytes, pos := 2735, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 48, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail40 :
    instructionSequenceAt 196 false { bytes := artifactBytes, pos := 2719, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 40, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail32 :
    instructionSequenceAt 204 false { bytes := artifactBytes, pos := 2700, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 32, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail24 :
    instructionSequenceAt 212 false { bytes := artifactBytes, pos := 2684, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 24, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail16 :
    instructionSequenceAt 220 false { bytes := artifactBytes, pos := 2668, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 16, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail8 :
    instructionSequenceAt 228 false { bytes := artifactBytes, pos := 2652, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

@[cbv_eval] theorem sequence17_tail0 :
    instructionSequenceAt 236 false { bytes := artifactBytes, pos := 2636, limit := 2872 } =
      .ok (((Cache.raw.codes[17]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2872, limit := 2872 }) := by cbv

theorem code17_decoded_parts :
    code { bytes := artifactBytes, pos := 2631, limit := 16006 } = .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2872, limit := 16006 }) := by
  refine code_eq_of_parts (size := 239)
    (payload := { bytes := artifactBytes, pos := 2633, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2636, limit := 2872 })
    (bodyFinish := { bytes := artifactBytes, pos := 2872, limit := 2872 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence17_tail0
  · rfl

#print axioms code17_decoded_parts
end Project.TinyGpt2Hidden.Artifact
