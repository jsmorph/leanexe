import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code65_seq_65_12_t_53_t_53_t_27_t_tail88_decoded :
    instructionSequenceAt 929 true { bytes := artifactBytes, pos := 7973, limit := 8553 } =
      .ok ((((((((((((Cache.raw.codes[65]!).body)[12]!).childBody false)[53]!).childBody false)[53]!).childBody false)[27]!).childBody false).drop 88, .otherwise), { bytes := artifactBytes, pos := 8229, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_53_t_53_t_27_t_tail0_decoded :
    instructionSequenceAt 1017 true { bytes := artifactBytes, pos := 7725, limit := 8553 } =
      .ok ((((((((((((Cache.raw.codes[65]!).body)[12]!).childBody false)[53]!).childBody false)[53]!).childBody false)[27]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8229, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_53_t_53_t_tail27_decoded :
    instructionSequenceAt 1019 true { bytes := artifactBytes, pos := 7723, limit := 8553 } =
      .ok ((((((((((Cache.raw.codes[65]!).body)[12]!).childBody false)[53]!).childBody false)[53]!).childBody false).drop 27, .otherwise), { bytes := artifactBytes, pos := 8301, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_53_t_53_t_tail0_decoded :
    instructionSequenceAt 1046 true { bytes := artifactBytes, pos := 7644, limit := 8553 } =
      .ok ((((((((((Cache.raw.codes[65]!).body)[12]!).childBody false)[53]!).childBody false)[53]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8301, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_53_t_tail53_decoded :
    instructionSequenceAt 1048 true { bytes := artifactBytes, pos := 7642, limit := 8553 } =
      .ok ((((((((Cache.raw.codes[65]!).body)[12]!).childBody false)[53]!).childBody false).drop 53, .otherwise), { bytes := artifactBytes, pos := 8377, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_53_t_tail0_decoded :
    instructionSequenceAt 1101 true { bytes := artifactBytes, pos := 7528, limit := 8553 } =
      .ok ((((((((Cache.raw.codes[65]!).body)[12]!).childBody false)[53]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8377, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_tail53_decoded :
    instructionSequenceAt 1103 true { bytes := artifactBytes, pos := 7526, limit := 8553 } =
      .ok ((((((Cache.raw.codes[65]!).body)[12]!).childBody false).drop 53, .otherwise), { bytes := artifactBytes, pos := 8453, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_12_t_tail0_decoded :
    instructionSequenceAt 1156 true { bytes := artifactBytes, pos := 7412, limit := 8553 } =
      .ok ((((((Cache.raw.codes[65]!).body)[12]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8453, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_tail12_decoded :
    instructionSequenceAt 1158 false { bytes := artifactBytes, pos := 7410, limit := 8553 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 12, .end), { bytes := artifactBytes, pos := 8553, limit := 8553 }) := by
  cbv

@[cbv_eval] theorem code65_seq_65_tail0_decoded :
    instructionSequenceAt 1170 false { bytes := artifactBytes, pos := 7383, limit := 8553 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8553, limit := 8553 }) := by
  cbv

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 7377, limit := 21767 } =
      .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 8553, limit := 21767 }) := by
  refine code_eq_of_parts (size := 1174)
    (payload := { bytes := artifactBytes, pos := 7379, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 7383, limit := 8553 })
    (bodyFinish := { bytes := artifactBytes, pos := 8553, limit := 8553 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code65_seq_65_tail0_decoded
  · rfl

#print axioms code65_decoded

end Project.EulerRiemann.Artifact
