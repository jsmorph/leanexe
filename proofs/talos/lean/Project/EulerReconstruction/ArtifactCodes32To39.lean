import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 3000, limit := 3061 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3061, limit := 3061 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 2996, limit := 5619 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3061, limit := 5619 }) := by
  refine code_eq_of_parts (size := 64)
    (payload := { bytes := artifactBytes, pos := 2997, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3000, limit := 3061 })
    (bodyFinish := { bytes := artifactBytes, pos := 3061, limit := 3061 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 3065, limit := 3114 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3114, limit := 3114 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3061, limit := 5619 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 3114, limit := 5619 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 3062, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3065, limit := 3114 })
    (bodyFinish := { bytes := artifactBytes, pos := 3114, limit := 3114 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 3118, limit := 3167 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3167, limit := 3167 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 3114, limit := 5619 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 3167, limit := 5619 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 3115, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3118, limit := 3167 })
    (bodyFinish := { bytes := artifactBytes, pos := 3167, limit := 3167 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 81 false { bytes := artifactBytes, pos := 3171, limit := 3252 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3252, limit := 3252 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 3167, limit := 5619 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 3252, limit := 5619 }) := by
  refine code_eq_of_parts (size := 84)
    (payload := { bytes := artifactBytes, pos := 3168, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3171, limit := 3252 })
    (bodyFinish := { bytes := artifactBytes, pos := 3252, limit := 3252 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_tail118_decoded :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 3603, limit := 3731 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 118, .end), { bytes := artifactBytes, pos := 3731, limit := 3731 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail109_decoded :
    instructionSequenceAt 365 false { bytes := artifactBytes, pos := 3473, limit := 3731 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 109, .end), { bytes := artifactBytes, pos := 3731, limit := 3731 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail44_decoded :
    instructionSequenceAt 430 false { bytes := artifactBytes, pos := 3345, limit := 3731 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 44, .end), { bytes := artifactBytes, pos := 3731, limit := 3731 }) := by
  cbv

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 474 false { bytes := artifactBytes, pos := 3257, limit := 3731 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3731, limit := 3731 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 3252, limit := 5619 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 3731, limit := 5619 }) := by
  refine code_eq_of_parts (size := 477)
    (payload := { bytes := artifactBytes, pos := 3254, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3257, limit := 3731 })
    (bodyFinish := { bytes := artifactBytes, pos := 3731, limit := 3731 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 3735, limit := 3742 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3742, limit := 3742 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 3731, limit := 5619 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 3742, limit := 5619 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 3732, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3735, limit := 3742 })
    (bodyFinish := { bytes := artifactBytes, pos := 3742, limit := 3742 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_2_t_0_t_75_e_tail1_decoded :
    instructionSequenceAt 385 false { bytes := artifactBytes, pos := 3968, limit := 4216 } =
      .ok ((((((((((Cache.raw.codes[38]!).body)[2]!).childBody false)[0]!).childBody false)[75]!).childBody true).drop 1, .end), { bytes := artifactBytes, pos := 4096, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_2_t_0_t_75_e_tail0_decoded :
    instructionSequenceAt 386 false { bytes := artifactBytes, pos := 3966, limit := 4216 } =
      .ok ((((((((((Cache.raw.codes[38]!).body)[2]!).childBody false)[0]!).childBody false)[75]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 4096, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_2_t_0_t_tail75_decoded :
    instructionSequenceAt 388 false { bytes := artifactBytes, pos := 3919, limit := 4216 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[2]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := artifactBytes, pos := 4099, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_2_t_0_t_tail15_decoded :
    instructionSequenceAt 448 false { bytes := artifactBytes, pos := 3791, limit := 4216 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[2]!).childBody false)[0]!).childBody false).drop 15, .end), { bytes := artifactBytes, pos := 4099, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_2_t_0_t_tail0_decoded :
    instructionSequenceAt 463 false { bytes := artifactBytes, pos := 3755, limit := 4216 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[2]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4099, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_2_t_tail0_decoded :
    instructionSequenceAt 465 false { bytes := artifactBytes, pos := 3753, limit := 4216 } =
      .ok ((((((Cache.raw.codes[38]!).body)[2]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4100, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail2_decoded :
    instructionSequenceAt 467 false { bytes := artifactBytes, pos := 3751, limit := 4216 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 2, .end), { bytes := artifactBytes, pos := 4216, limit := 4216 }) := by
  cbv

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 469 false { bytes := artifactBytes, pos := 3747, limit := 4216 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4216, limit := 4216 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 3742, limit := 5619 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 4216, limit := 5619 }) := by
  refine code_eq_of_parts (size := 472)
    (payload := { bytes := artifactBytes, pos := 3744, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 3747, limit := 4216 })
    (bodyFinish := { bytes := artifactBytes, pos := 4216, limit := 4216 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 4220, limit := 4245 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4245, limit := 4245 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 4216, limit := 5619 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 4245, limit := 5619 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 4217, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 4220, limit := 4245 })
    (bodyFinish := { bytes := artifactBytes, pos := 4245, limit := 4245 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded


end Project.EulerReconstruction.Artifact
