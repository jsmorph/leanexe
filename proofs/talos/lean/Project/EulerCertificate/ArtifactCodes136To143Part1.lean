import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes136To143Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code142_seq_142_16_t_17_t_31_t_tail4_decoded :
    instructionSequenceAt 807 true { bytes := artifactBytes, pos := 28848, limit := 29501 } =
      .ok ((((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 4, .otherwise), { bytes := artifactBytes, pos := 29326, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_17_t_31_t_tail0_decoded :
    instructionSequenceAt 811 true { bytes := artifactBytes, pos := 28840, limit := 29501 } =
      .ok ((((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false)[31]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 29326, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_17_t_tail31_decoded :
    instructionSequenceAt 813 true { bytes := artifactBytes, pos := 28838, limit := 29501 } =
      .ok ((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false).drop 31, .otherwise), { bytes := artifactBytes, pos := 29379, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_17_t_tail0_decoded :
    instructionSequenceAt 844 true { bytes := artifactBytes, pos := 28747, limit := 29501 } =
      .ok ((((((((Cache.raw.codes[142]!).body)[16]!).childBody false)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 29379, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_tail17_decoded :
    instructionSequenceAt 846 true { bytes := artifactBytes, pos := 28745, limit := 29501 } =
      .ok ((((((Cache.raw.codes[142]!).body)[16]!).childBody false).drop 17, .otherwise), { bytes := artifactBytes, pos := 29432, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_16_t_tail0_decoded :
    instructionSequenceAt 863 true { bytes := artifactBytes, pos := 28703, limit := 29501 } =
      .ok ((((((Cache.raw.codes[142]!).body)[16]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 29432, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_tail16_decoded :
    instructionSequenceAt 865 false { bytes := artifactBytes, pos := 28701, limit := 29501 } =
      .ok ((((Cache.raw.codes[142]!).body).drop 16, .end), { bytes := artifactBytes, pos := 29501, limit := 29501 }) := by
  cbv

@[cbv_eval] theorem code142_seq_142_tail0_decoded :
    instructionSequenceAt 881 false { bytes := artifactBytes, pos := 28620, limit := 29501 } =
      .ok ((((Cache.raw.codes[142]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29501, limit := 29501 }) := by
  cbv

theorem code142_decoded :
    code { bytes := artifactBytes, pos := 28615, limit := 45644 } =
      .ok (Cache.raw.codes[142]!, { bytes := artifactBytes, pos := 29501, limit := 45644 }) := by
  refine code_eq_of_parts (size := 884)
    (payload := { bytes := artifactBytes, pos := 28617, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28620, limit := 29501 })
    (bodyFinish := { bytes := artifactBytes, pos := 29501, limit := 29501 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code142_seq_142_tail0_decoded
  · rfl

#print axioms code142_decoded

@[cbv_eval] theorem code143_seq_143_tail107_decoded :
    instructionSequenceAt 237 false { bytes := artifactBytes, pos := 29722, limit := 29850 } =
      .ok ((((Cache.raw.codes[143]!).body).drop 107, .end), { bytes := artifactBytes, pos := 29850, limit := 29850 }) := by
  cbv

@[cbv_eval] theorem code143_seq_143_tail43_decoded :
    instructionSequenceAt 301 false { bytes := artifactBytes, pos := 29593, limit := 29850 } =
      .ok ((((Cache.raw.codes[143]!).body).drop 43, .end), { bytes := artifactBytes, pos := 29850, limit := 29850 }) := by
  cbv

@[cbv_eval] theorem code143_seq_143_tail0_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 29506, limit := 29850 } =
      .ok ((((Cache.raw.codes[143]!).body).drop 0, .end), { bytes := artifactBytes, pos := 29850, limit := 29850 }) := by
  cbv

theorem code143_decoded :
    code { bytes := artifactBytes, pos := 29501, limit := 45644 } =
      .ok (Cache.raw.codes[143]!, { bytes := artifactBytes, pos := 29850, limit := 45644 }) := by
  refine code_eq_of_parts (size := 347)
    (payload := { bytes := artifactBytes, pos := 29503, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 29506, limit := 29850 })
    (bodyFinish := { bytes := artifactBytes, pos := 29850, limit := 29850 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code143_seq_143_tail0_decoded
  · rfl

#print axioms code143_decoded

end Project.EulerCertificate.Artifact
