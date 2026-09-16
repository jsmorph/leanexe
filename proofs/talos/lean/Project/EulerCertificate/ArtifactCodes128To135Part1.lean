import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes128To135Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code133_seq_133_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 28208, limit := 28215 } =
      .ok ((((Cache.raw.codes[133]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28215, limit := 28215 }) := by
  cbv

theorem code133_decoded :
    code { bytes := artifactBytes, pos := 28204, limit := 45644 } =
      .ok (Cache.raw.codes[133]!, { bytes := artifactBytes, pos := 28215, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 28205, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28208, limit := 28215 })
    (bodyFinish := { bytes := artifactBytes, pos := 28215, limit := 28215 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code133_seq_133_tail0_decoded
  · rfl

#print axioms code133_decoded

@[cbv_eval] theorem code134_seq_134_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 28219, limit := 28226 } =
      .ok ((((Cache.raw.codes[134]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28226, limit := 28226 }) := by
  cbv

theorem code134_decoded :
    code { bytes := artifactBytes, pos := 28215, limit := 45644 } =
      .ok (Cache.raw.codes[134]!, { bytes := artifactBytes, pos := 28226, limit := 45644 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 28216, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28219, limit := 28226 })
    (bodyFinish := { bytes := artifactBytes, pos := 28226, limit := 28226 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code134_seq_134_tail0_decoded
  · rfl

#print axioms code134_decoded

@[cbv_eval] theorem code135_seq_135_17_t_tail0_decoded :
    instructionSequenceAt 220 true { bytes := artifactBytes, pos := 28322, limit := 28470 } =
      .ok ((((((Cache.raw.codes[135]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 28450, limit := 28470 }) := by
  cbv

@[cbv_eval] theorem code135_seq_135_tail17_decoded :
    instructionSequenceAt 222 false { bytes := artifactBytes, pos := 28320, limit := 28470 } =
      .ok ((((Cache.raw.codes[135]!).body).drop 17, .end), { bytes := artifactBytes, pos := 28470, limit := 28470 }) := by
  cbv

@[cbv_eval] theorem code135_seq_135_tail0_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 28231, limit := 28470 } =
      .ok ((((Cache.raw.codes[135]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28470, limit := 28470 }) := by
  cbv

theorem code135_decoded :
    code { bytes := artifactBytes, pos := 28226, limit := 45644 } =
      .ok (Cache.raw.codes[135]!, { bytes := artifactBytes, pos := 28470, limit := 45644 }) := by
  refine code_eq_of_parts (size := 242)
    (payload := { bytes := artifactBytes, pos := 28228, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 28231, limit := 28470 })
    (bodyFinish := { bytes := artifactBytes, pos := 28470, limit := 28470 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code135_seq_135_tail0_decoded
  · rfl

#print axioms code135_decoded

end Project.EulerCertificate.Artifact
