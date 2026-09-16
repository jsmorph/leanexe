import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes168To175Part1

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code173_seq_173_78_t_0_t_tail0_decoded :
    instructionSequenceAt 830 false { bytes := artifactBytes, pos := 37424, limit := 38160 } =
      .ok ((((((((Cache.raw.codes[173]!).body)[78]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 38066, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_78_t_tail0_decoded :
    instructionSequenceAt 832 false { bytes := artifactBytes, pos := 37422, limit := 38160 } =
      .ok ((((((Cache.raw.codes[173]!).body)[78]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 38067, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_tail78_decoded :
    instructionSequenceAt 834 false { bytes := artifactBytes, pos := 37420, limit := 38160 } =
      .ok ((((Cache.raw.codes[173]!).body).drop 78, .end), { bytes := artifactBytes, pos := 38160, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_tail22_decoded :
    instructionSequenceAt 890 false { bytes := artifactBytes, pos := 37292, limit := 38160 } =
      .ok ((((Cache.raw.codes[173]!).body).drop 22, .end), { bytes := artifactBytes, pos := 38160, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_tail0_decoded :
    instructionSequenceAt 912 false { bytes := artifactBytes, pos := 37248, limit := 38160 } =
      .ok ((((Cache.raw.codes[173]!).body).drop 0, .end), { bytes := artifactBytes, pos := 38160, limit := 38160 }) := by
  cbv

theorem code173_decoded :
    code { bytes := artifactBytes, pos := 37242, limit := 45644 } =
      .ok (Cache.raw.codes[173]!, { bytes := artifactBytes, pos := 38160, limit := 45644 }) := by
  refine code_eq_of_parts (size := 916)
    (payload := { bytes := artifactBytes, pos := 37244, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 37248, limit := 38160 })
    (bodyFinish := { bytes := artifactBytes, pos := 38160, limit := 38160 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code173_seq_173_tail0_decoded
  · rfl

#print axioms code173_decoded

@[cbv_eval] theorem code174_seq_174_tail61_decoded :
    instructionSequenceAt 192 false { bytes := artifactBytes, pos := 38290, limit := 38418 } =
      .ok ((((Cache.raw.codes[174]!).body).drop 61, .end), { bytes := artifactBytes, pos := 38418, limit := 38418 }) := by
  cbv

@[cbv_eval] theorem code174_seq_174_tail0_decoded :
    instructionSequenceAt 253 false { bytes := artifactBytes, pos := 38165, limit := 38418 } =
      .ok ((((Cache.raw.codes[174]!).body).drop 0, .end), { bytes := artifactBytes, pos := 38418, limit := 38418 }) := by
  cbv

theorem code174_decoded :
    code { bytes := artifactBytes, pos := 38160, limit := 45644 } =
      .ok (Cache.raw.codes[174]!, { bytes := artifactBytes, pos := 38418, limit := 45644 }) := by
  refine code_eq_of_parts (size := 256)
    (payload := { bytes := artifactBytes, pos := 38162, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 38165, limit := 38418 })
    (bodyFinish := { bytes := artifactBytes, pos := 38418, limit := 38418 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code174_seq_174_tail0_decoded
  · rfl

#print axioms code174_decoded

@[cbv_eval] theorem code175_seq_175_tail267_decoded :
    instructionSequenceAt 407 false { bytes := artifactBytes, pos := 38968, limit := 39098 } =
      .ok ((((Cache.raw.codes[175]!).body).drop 267, .end), { bytes := artifactBytes, pos := 39098, limit := 39098 }) := by
  cbv

@[cbv_eval] theorem code175_seq_175_tail206_decoded :
    instructionSequenceAt 468 false { bytes := artifactBytes, pos := 38839, limit := 39098 } =
      .ok ((((Cache.raw.codes[175]!).body).drop 206, .end), { bytes := artifactBytes, pos := 39098, limit := 39098 }) := by
  cbv

@[cbv_eval] theorem code175_seq_175_tail142_decoded :
    instructionSequenceAt 532 false { bytes := artifactBytes, pos := 38710, limit := 39098 } =
      .ok ((((Cache.raw.codes[175]!).body).drop 142, .end), { bytes := artifactBytes, pos := 39098, limit := 39098 }) := by
  cbv

@[cbv_eval] theorem code175_seq_175_tail78_decoded :
    instructionSequenceAt 596 false { bytes := artifactBytes, pos := 38582, limit := 39098 } =
      .ok ((((Cache.raw.codes[175]!).body).drop 78, .end), { bytes := artifactBytes, pos := 39098, limit := 39098 }) := by
  cbv

@[cbv_eval] theorem code175_seq_175_tail15_decoded :
    instructionSequenceAt 659 false { bytes := artifactBytes, pos := 38454, limit := 39098 } =
      .ok ((((Cache.raw.codes[175]!).body).drop 15, .end), { bytes := artifactBytes, pos := 39098, limit := 39098 }) := by
  cbv

@[cbv_eval] theorem code175_seq_175_tail0_decoded :
    instructionSequenceAt 674 false { bytes := artifactBytes, pos := 38424, limit := 39098 } =
      .ok ((((Cache.raw.codes[175]!).body).drop 0, .end), { bytes := artifactBytes, pos := 39098, limit := 39098 }) := by
  cbv

theorem code175_decoded :
    code { bytes := artifactBytes, pos := 38418, limit := 45644 } =
      .ok (Cache.raw.codes[175]!, { bytes := artifactBytes, pos := 39098, limit := 45644 }) := by
  refine code_eq_of_parts (size := 678)
    (payload := { bytes := artifactBytes, pos := 38420, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 38424, limit := 39098 })
    (bodyFinish := { bytes := artifactBytes, pos := 39098, limit := 39098 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code175_seq_175_tail0_decoded
  · rfl

#print axioms code175_decoded

end Project.EulerCertificate.Artifact
