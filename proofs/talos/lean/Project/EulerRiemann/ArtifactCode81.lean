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

@[cbv_eval] theorem code81_seq_81_4_t_0_t_22_e_tail28_decoded :
    instructionSequenceAt 1068 false { bytes := artifactBytes, pos := 10841, limit := 11606 } =
      .ok ((((((((((Cache.raw.codes[81]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 11188, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_4_t_0_t_22_e_tail0_decoded :
    instructionSequenceAt 1096 false { bytes := artifactBytes, pos := 10787, limit := 11606 } =
      .ok ((((((((((Cache.raw.codes[81]!).body)[4]!).childBody false)[0]!).childBody false)[22]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 11188, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_4_t_0_t_tail22_decoded :
    instructionSequenceAt 1098 false { bytes := artifactBytes, pos := 10543, limit := 11606 } =
      .ok ((((((((Cache.raw.codes[81]!).body)[4]!).childBody false)[0]!).childBody false).drop 22, .end), { bytes := artifactBytes, pos := 11191, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_4_t_0_t_tail0_decoded :
    instructionSequenceAt 1120 false { bytes := artifactBytes, pos := 10490, limit := 11606 } =
      .ok ((((((((Cache.raw.codes[81]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11191, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_4_t_tail0_decoded :
    instructionSequenceAt 1122 false { bytes := artifactBytes, pos := 10488, limit := 11606 } =
      .ok ((((((Cache.raw.codes[81]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11192, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_8_t_tail28_decoded :
    instructionSequenceAt 1090 true { bytes := artifactBytes, pos := 11253, limit := 11606 } =
      .ok ((((((Cache.raw.codes[81]!).body)[8]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 11596, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_8_t_tail0_decoded :
    instructionSequenceAt 1118 true { bytes := artifactBytes, pos := 11199, limit := 11606 } =
      .ok ((((((Cache.raw.codes[81]!).body)[8]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 11596, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_tail8_decoded :
    instructionSequenceAt 1120 false { bytes := artifactBytes, pos := 11197, limit := 11606 } =
      .ok ((((Cache.raw.codes[81]!).body).drop 8, .end), { bytes := artifactBytes, pos := 11606, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_tail4_decoded :
    instructionSequenceAt 1124 false { bytes := artifactBytes, pos := 10486, limit := 11606 } =
      .ok ((((Cache.raw.codes[81]!).body).drop 4, .end), { bytes := artifactBytes, pos := 11606, limit := 11606 }) := by
  cbv

@[cbv_eval] theorem code81_seq_81_tail0_decoded :
    instructionSequenceAt 1128 false { bytes := artifactBytes, pos := 10478, limit := 11606 } =
      .ok ((((Cache.raw.codes[81]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11606, limit := 11606 }) := by
  cbv

theorem code81_decoded :
    code { bytes := artifactBytes, pos := 10473, limit := 21767 } =
      .ok (Cache.raw.codes[81]!, { bytes := artifactBytes, pos := 11606, limit := 21767 }) := by
  refine code_eq_of_parts (size := 1131)
    (payload := { bytes := artifactBytes, pos := 10475, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 10478, limit := 11606 })
    (bodyFinish := { bytes := artifactBytes, pos := 11606, limit := 11606 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code81_seq_81_tail0_decoded
  · rfl

#print axioms code81_decoded

end Project.EulerRiemann.Artifact
