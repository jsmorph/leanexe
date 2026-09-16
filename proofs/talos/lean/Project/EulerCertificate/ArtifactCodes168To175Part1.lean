import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodes168To175Part0

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code170_seq_170_tail55_decoded :
    instructionSequenceAt 967 false { bytes := artifactBytes, pos := 35552, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 55, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

@[cbv_eval] theorem code170_seq_170_tail0_decoded :
    instructionSequenceAt 1022 false { bytes := artifactBytes, pos := 35431, limit := 36453 } =
      .ok ((((Cache.raw.codes[170]!).body).drop 0, .end), { bytes := artifactBytes, pos := 36453, limit := 36453 }) := by
  cbv

theorem code170_decoded :
    code { bytes := artifactBytes, pos := 35425, limit := 45644 } =
      .ok (Cache.raw.codes[170]!, { bytes := artifactBytes, pos := 36453, limit := 45644 }) := by
  refine code_eq_of_parts (size := 1026)
    (payload := { bytes := artifactBytes, pos := 35427, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 35431, limit := 36453 })
    (bodyFinish := { bytes := artifactBytes, pos := 36453, limit := 36453 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code170_seq_170_tail0_decoded
  · rfl

#print axioms code170_decoded

@[cbv_eval] theorem code171_seq_171_tail85_decoded :
    instructionSequenceAt 216 false { bytes := artifactBytes, pos := 36631, limit := 36759 } =
      .ok ((((Cache.raw.codes[171]!).body).drop 85, .end), { bytes := artifactBytes, pos := 36759, limit := 36759 }) := by
  cbv

@[cbv_eval] theorem code171_seq_171_tail22_decoded :
    instructionSequenceAt 279 false { bytes := artifactBytes, pos := 36503, limit := 36759 } =
      .ok ((((Cache.raw.codes[171]!).body).drop 22, .end), { bytes := artifactBytes, pos := 36759, limit := 36759 }) := by
  cbv

@[cbv_eval] theorem code171_seq_171_tail0_decoded :
    instructionSequenceAt 301 false { bytes := artifactBytes, pos := 36458, limit := 36759 } =
      .ok ((((Cache.raw.codes[171]!).body).drop 0, .end), { bytes := artifactBytes, pos := 36759, limit := 36759 }) := by
  cbv

theorem code171_decoded :
    code { bytes := artifactBytes, pos := 36453, limit := 45644 } =
      .ok (Cache.raw.codes[171]!, { bytes := artifactBytes, pos := 36759, limit := 45644 }) := by
  refine code_eq_of_parts (size := 304)
    (payload := { bytes := artifactBytes, pos := 36455, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 36458, limit := 36759 })
    (bodyFinish := { bytes := artifactBytes, pos := 36759, limit := 36759 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code171_seq_171_tail0_decoded
  · rfl

#print axioms code171_decoded

@[cbv_eval] theorem code172_seq_172_tail174_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 37114, limit := 37242 } =
      .ok ((((Cache.raw.codes[172]!).body).drop 174, .end), { bytes := artifactBytes, pos := 37242, limit := 37242 }) := by
  cbv

@[cbv_eval] theorem code172_seq_172_tail110_decoded :
    instructionSequenceAt 368 false { bytes := artifactBytes, pos := 36986, limit := 37242 } =
      .ok ((((Cache.raw.codes[172]!).body).drop 110, .end), { bytes := artifactBytes, pos := 37242, limit := 37242 }) := by
  cbv

@[cbv_eval] theorem code172_seq_172_tail46_decoded :
    instructionSequenceAt 432 false { bytes := artifactBytes, pos := 36857, limit := 37242 } =
      .ok ((((Cache.raw.codes[172]!).body).drop 46, .end), { bytes := artifactBytes, pos := 37242, limit := 37242 }) := by
  cbv

@[cbv_eval] theorem code172_seq_172_tail0_decoded :
    instructionSequenceAt 478 false { bytes := artifactBytes, pos := 36764, limit := 37242 } =
      .ok ((((Cache.raw.codes[172]!).body).drop 0, .end), { bytes := artifactBytes, pos := 37242, limit := 37242 }) := by
  cbv

theorem code172_decoded :
    code { bytes := artifactBytes, pos := 36759, limit := 45644 } =
      .ok (Cache.raw.codes[172]!, { bytes := artifactBytes, pos := 37242, limit := 45644 }) := by
  refine code_eq_of_parts (size := 481)
    (payload := { bytes := artifactBytes, pos := 36761, limit := 45644 })
    (bodyStart := { bytes := artifactBytes, pos := 36764, limit := 37242 })
    (bodyFinish := { bytes := artifactBytes, pos := 37242, limit := 37242 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code172_seq_172_tail0_decoded
  · rfl

#print axioms code172_decoded

@[cbv_eval] theorem code173_seq_173_78_t_0_t_tail261_decoded :
    instructionSequenceAt 569 false { bytes := artifactBytes, pos := 37938, limit := 38160 } =
      .ok ((((((((Cache.raw.codes[173]!).body)[78]!).childBody false)[0]!).childBody false).drop 261, .end), { bytes := artifactBytes, pos := 38066, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_78_t_0_t_tail199_decoded :
    instructionSequenceAt 631 false { bytes := artifactBytes, pos := 37810, limit := 38160 } =
      .ok ((((((((Cache.raw.codes[173]!).body)[78]!).childBody false)[0]!).childBody false).drop 199, .end), { bytes := artifactBytes, pos := 38066, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_78_t_0_t_tail135_decoded :
    instructionSequenceAt 695 false { bytes := artifactBytes, pos := 37682, limit := 38160 } =
      .ok ((((((((Cache.raw.codes[173]!).body)[78]!).childBody false)[0]!).childBody false).drop 135, .end), { bytes := artifactBytes, pos := 38066, limit := 38160 }) := by
  cbv

@[cbv_eval] theorem code173_seq_173_78_t_0_t_tail69_decoded :
    instructionSequenceAt 761 false { bytes := artifactBytes, pos := 37554, limit := 38160 } =
      .ok ((((((((Cache.raw.codes[173]!).body)[78]!).childBody false)[0]!).childBody false).drop 69, .end), { bytes := artifactBytes, pos := 38066, limit := 38160 }) := by
  cbv

end Project.EulerCertificate.Artifact
