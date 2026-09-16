import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code136_seq_136_tail0_decoded :
    instructionSequenceAt 44 false { bytes := artifactBytes, pos := 28474, limit := 28518 } =
      .ok ((((Cache.raw.codes[136]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28518, limit := 28518 }) := by
  cbv

theorem code136_decoded :
    code { bytes := artifactBytes, pos := 28470, limit := 45644 } =
      .ok (Cache.raw.codes[136]!, { bytes := artifactBytes, pos := 28518, limit := 45644 }) := by
  refine code_eq_of_parts (size := 47)
    (payload := { bytes := artifactBytes, pos := 28471, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28474, limit := 28518 })
    (bodyFinish := { bytes := artifactBytes, pos := 28518, limit := 28518 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code136_seq_136_tail0_decoded
  · rfl

#print axioms code136_decoded

@[cbv_eval] theorem code137_seq_137_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 28522, limit := 28529 } =
      .ok ((((Cache.raw.codes[137]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28529, limit := 28529 }) := by
  cbv

theorem code137_decoded :
    code { bytes := artifactBytes, pos := 28518, limit := 45644 } =
      .ok (Cache.raw.codes[137]!, { bytes := artifactBytes, pos := 28529, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 28519, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28522, limit := 28529 })
    (bodyFinish := { bytes := artifactBytes, pos := 28529, limit := 28529 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code137_seq_137_tail0_decoded
  · rfl

#print axioms code137_decoded

@[cbv_eval] theorem code138_seq_138_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 28533, limit := 28540 } =
      .ok ((((Cache.raw.codes[138]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28540, limit := 28540 }) := by
  cbv

theorem code138_decoded :
    code { bytes := artifactBytes, pos := 28529, limit := 45644 } =
      .ok (Cache.raw.codes[138]!, { bytes := artifactBytes, pos := 28540, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 28530, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28533, limit := 28540 })
    (bodyFinish := { bytes := artifactBytes, pos := 28540, limit := 28540 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code138_seq_138_tail0_decoded
  · rfl

#print axioms code138_decoded

@[cbv_eval] theorem code139_seq_139_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 28544, limit := 28551 } =
      .ok ((((Cache.raw.codes[139]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28551, limit := 28551 }) := by
  cbv

theorem code139_decoded :
    code { bytes := artifactBytes, pos := 28540, limit := 45644 } =
      .ok (Cache.raw.codes[139]!, { bytes := artifactBytes, pos := 28551, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 28541, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28544, limit := 28551 })
    (bodyFinish := { bytes := artifactBytes, pos := 28551, limit := 28551 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code139_seq_139_tail0_decoded
  · rfl

#print axioms code139_decoded

@[cbv_eval] theorem code140_seq_140_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 28555, limit := 28562 } =
      .ok ((((Cache.raw.codes[140]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28562, limit := 28562 }) := by
  cbv

theorem code140_decoded :
    code { bytes := artifactBytes, pos := 28551, limit := 45644 } =
      .ok (Cache.raw.codes[140]!, { bytes := artifactBytes, pos := 28562, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 28552, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28555, limit := 28562 })
    (bodyFinish := { bytes := artifactBytes, pos := 28562, limit := 28562 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code140_seq_140_tail0_decoded
  · rfl

#print axioms code140_decoded

@[cbv_eval] theorem code141_seq_141_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 28566, limit := 28615 } =
      .ok ((((Cache.raw.codes[141]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28615, limit := 28615 }) := by
  cbv

theorem code141_decoded :
    code { bytes := artifactBytes, pos := 28562, limit := 45644 } =
      .ok (Cache.raw.codes[141]!, { bytes := artifactBytes, pos := 28615, limit := 45644 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 28563, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28566, limit := 28615 })
    (bodyFinish := { bytes := artifactBytes, pos := 28615, limit := 28615 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code141_seq_141_tail0_decoded
  · rfl

#print axioms code141_decoded

@[cbv_eval] theorem code142_seq_142_16_t_17_t_31_t_93_t_tail19_decoded :
    instructionSequenceAt 697 true { bytes := artifactBytes, pos := 29145, limit := 29501 } =
      .ok ((((((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false)[93]!).childBody false).drop 19, .otherwise), { bytes := artifactBytes, pos := 29273, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_17_t_31_t_93_t_tail0_decoded :
    instructionSequenceAt 716 true { bytes := artifactBytes, pos := 29107, limit := 29501 } =
      .ok ((((((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false)[93]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 29273, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_17_t_31_t_tail93_decoded :
    instructionSequenceAt 718 true { bytes := artifactBytes, pos := 29105, limit := 29501 } =
      .ok ((((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 93, .otherwise), { bytes := artifactBytes, pos := 29326, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_17_t_31_t_tail67_decoded :
    instructionSequenceAt 744 true { bytes := artifactBytes, pos := 28977, limit := 29501 } =
      .ok ((((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 67, .otherwise), { bytes := artifactBytes, pos := 29326, limit := 29501 }) := by
  cbv

end Project.EulerCertificate.Artifact
