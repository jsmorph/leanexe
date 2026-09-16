import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes40To47Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code46_seq_46_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 10061, limit := 10110 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10110, limit := 10110 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 10057, limit := 45644 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 10110, limit := 45644 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 10058, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 10061, limit := 10110 })
    (bodyFinish := { bytes := artifactBytes, pos := 10110, limit := 10110 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_seq_46_tail0_decoded
  · rfl

#print axioms code46_decoded

@[cbv_eval] theorem code47_seq_47_21_t_69_t_37_t_tail54_decoded :
    instructionSequenceAt 649 true { bytes := artifactBytes, pos := 10651, limit := 10951 } =
      .ok ((((((((((Cache.raw.codes[47]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 54, .otherwise), { bytes := artifactBytes, pos := 10779, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_69_t_37_t_tail12_decoded :
    instructionSequenceAt 691 true { bytes := artifactBytes, pos := 10523, limit := 10951 } =
      .ok ((((((((((Cache.raw.codes[47]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 12, .otherwise), { bytes := artifactBytes, pos := 10779, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_69_t_37_t_tail0_decoded :
    instructionSequenceAt 703 true { bytes := artifactBytes, pos := 10504, limit := 10951 } =
      .ok ((((((((((Cache.raw.codes[47]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 10779, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_69_t_tail37_decoded :
    instructionSequenceAt 705 true { bytes := artifactBytes, pos := 10502, limit := 10951 } =
      .ok ((((((((Cache.raw.codes[47]!).body)[21]!).childBody false)[69]!).childBody false).drop 37, .otherwise), { bytes := artifactBytes, pos := 10831, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_69_t_tail0_decoded :
    instructionSequenceAt 742 true { bytes := artifactBytes, pos := 10385, limit := 10951 } =
      .ok ((((((((Cache.raw.codes[47]!).body)[21]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 10831, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_tail69_decoded :
    instructionSequenceAt 744 true { bytes := artifactBytes, pos := 10383, limit := 10951 } =
      .ok ((((((Cache.raw.codes[47]!).body)[21]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 10883, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_tail56_decoded :
    instructionSequenceAt 757 true { bytes := artifactBytes, pos := 10252, limit := 10951 } =
      .ok ((((((Cache.raw.codes[47]!).body)[21]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 10883, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_21_t_tail0_decoded :
    instructionSequenceAt 813 true { bytes := artifactBytes, pos := 10162, limit := 10951 } =
      .ok ((((((Cache.raw.codes[47]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 10883, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_tail21_decoded :
    instructionSequenceAt 815 false { bytes := artifactBytes, pos := 10160, limit := 10951 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 21, .end), { bytes := artifactBytes, pos := 10951, limit := 10951 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_tail0_decoded :
    instructionSequenceAt 836 false { bytes := artifactBytes, pos := 10115, limit := 10951 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10951, limit := 10951 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 10110, limit := 45644 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 10951, limit := 45644 }) := by
  refine code_eq_of_parts (size := 839)
    (payload := { bytes := artifactBytes, pos := 10112, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 10115, limit := 10951 })
    (bodyFinish := { bytes := artifactBytes, pos := 10951, limit := 10951 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code47_seq_47_tail0_decoded
  · rfl

#print axioms code47_decoded

end Project.EulerCertificate.Artifact
