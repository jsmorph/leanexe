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

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_53_t_0_t_tail72_decoded :
    instructionSequenceAt 2380 false { bytes := artifactBytes, pos := 14984, limit := 16415 } =
      .ok ((((((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 72, .end), { bytes := artifactBytes, pos := 15240, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_53_t_0_t_tail0_decoded :
    instructionSequenceAt 2452 false { bytes := artifactBytes, pos := 14864, limit := 16415 } =
      .ok ((((((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15240, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_53_t_tail0_decoded :
    instructionSequenceAt 2454 false { bytes := artifactBytes, pos := 14862, limit := 16415 } =
      .ok ((((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true)[53]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15241, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_t_tail52_decoded :
    instructionSequenceAt 2457 true { bytes := artifactBytes, pos := 14042, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 52, .otherwise), { bytes := artifactBytes, pos := 14452, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_t_tail0_decoded :
    instructionSequenceAt 2509 true { bytes := artifactBytes, pos := 13929, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 14452, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_tail114_decoded :
    instructionSequenceAt 2395 false { bytes := artifactBytes, pos := 15517, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 114, .end), { bytes := artifactBytes, pos := 15879, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_tail64_decoded :
    instructionSequenceAt 2445 false { bytes := artifactBytes, pos := 15261, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 64, .end), { bytes := artifactBytes, pos := 15879, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_tail53_decoded :
    instructionSequenceAt 2456 false { bytes := artifactBytes, pos := 14860, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 53, .end), { bytes := artifactBytes, pos := 15879, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_tail36_decoded :
    instructionSequenceAt 2473 false { bytes := artifactBytes, pos := 14522, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 36, .end), { bytes := artifactBytes, pos := 15879, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_14_e_tail0_decoded :
    instructionSequenceAt 2509 false { bytes := artifactBytes, pos := 14452, limit := 16415 } =
      .ok ((((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 15879, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_tail14_decoded :
    instructionSequenceAt 2511 false { bytes := artifactBytes, pos := 13927, limit := 16415 } =
      .ok ((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 15882, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_0_t_tail0_decoded :
    instructionSequenceAt 2525 false { bytes := artifactBytes, pos := 13894, limit := 16415 } =
      .ok ((((((((Cache.raw.codes[95]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15882, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_4_t_tail0_decoded :
    instructionSequenceAt 2527 false { bytes := artifactBytes, pos := 13892, limit := 16415 } =
      .ok ((((((Cache.raw.codes[95]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15883, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_8_t_tail52_decoded :
    instructionSequenceAt 2471 true { bytes := artifactBytes, pos := 16003, limit := 16415 } =
      .ok ((((((Cache.raw.codes[95]!).body)[8]!).childBody false).drop 52, .otherwise), { bytes := artifactBytes, pos := 16409, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_8_t_tail0_decoded :
    instructionSequenceAt 2523 true { bytes := artifactBytes, pos := 15890, limit := 16415 } =
      .ok ((((((Cache.raw.codes[95]!).body)[8]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 16409, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_tail8_decoded :
    instructionSequenceAt 2525 false { bytes := artifactBytes, pos := 15888, limit := 16415 } =
      .ok ((((Cache.raw.codes[95]!).body).drop 8, .end), { bytes := artifactBytes, pos := 16415, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_tail4_decoded :
    instructionSequenceAt 2529 false { bytes := artifactBytes, pos := 13890, limit := 16415 } =
      .ok ((((Cache.raw.codes[95]!).body).drop 4, .end), { bytes := artifactBytes, pos := 16415, limit := 16415 }) := by
  cbv

@[cbv_eval] theorem code95_seq_95_tail0_decoded :
    instructionSequenceAt 2533 false { bytes := artifactBytes, pos := 13882, limit := 16415 } =
      .ok ((((Cache.raw.codes[95]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16415, limit := 16415 }) := by
  cbv

theorem code95_decoded :
    code { bytes := artifactBytes, pos := 13877, limit := 21767 } =
      .ok (Cache.raw.codes[95]!, { bytes := artifactBytes, pos := 16415, limit := 21767 }) := by
  refine code_eq_of_parts (size := 2536)
    (payload := { bytes := artifactBytes, pos := 13879, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 13882, limit := 16415 })
    (bodyFinish := { bytes := artifactBytes, pos := 16415, limit := 16415 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code95_seq_95_tail0_decoded
  · rfl

#print axioms code95_decoded

end Project.EulerRiemann.Artifact
