import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_10_e_7_t_24_t_0_t_tail18 :
    instructionSequenceAt 3311 false { bytes := bytes, pos := 8155, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 8283, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_24_t_0_t_tail0 :
    instructionSequenceAt 3329 false { bytes := bytes, pos := 8124, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8283, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_79_t_0_t_tail18 :
    instructionSequenceAt 3256 false { bytes := bytes, pos := 8566, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[79]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 8694, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_79_t_0_t_tail0 :
    instructionSequenceAt 3274 false { bytes := bytes, pos := 8535, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[79]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8694, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_137_t_0_t_tail18 :
    instructionSequenceAt 3198 false { bytes := bytes, pos := 9031, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[137]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 9159, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_137_t_0_t_tail0 :
    instructionSequenceAt 3216 false { bytes := bytes, pos := 9000, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[137]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9159, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_192_t_0_t_tail18 :
    instructionSequenceAt 3143 false { bytes := bytes, pos := 9523, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[192]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 9651, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_192_t_0_t_tail0 :
    instructionSequenceAt 3161 false { bytes := bytes, pos := 9492, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[192]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9651, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_34_t_0_t_tail18 :
    instructionSequenceAt 3301 false { bytes := bytes, pos := 10119, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 10247, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_34_t_0_t_tail0 :
    instructionSequenceAt 3319 false { bytes := bytes, pos := 10088, limit := 10494 } =
      .ok ((((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 10247, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_24_t_0_t_tail18 :
    instructionSequenceAt 3320 false { bytes := bytes, pos := 7227, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 7355, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_24_t_0_t_tail0 :
    instructionSequenceAt 3338 false { bytes := bytes, pos := 7196, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7355, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_93_t_0_t_tail18 :
    instructionSequenceAt 3251 false { bytes := bytes, pos := 7662, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[93]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := bytes, pos := 7790, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_93_t_0_t_tail0 :
    instructionSequenceAt 3269 false { bytes := bytes, pos := 7631, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody false)[93]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7790, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_24_t_tail0 :
    instructionSequenceAt 3331 false { bytes := bytes, pos := 8122, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8284, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_28_t_tail8 :
    instructionSequenceAt 3319 true { bytes := bytes, pos := 8304, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := bytes, pos := 8435, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_28_t_tail0 :
    instructionSequenceAt 3327 true { bytes := bytes, pos := 8291, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8435, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_79_t_tail0 :
    instructionSequenceAt 3276 false { bytes := bytes, pos := 8533, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[79]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8695, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_83_t_tail8 :
    instructionSequenceAt 3264 true { bytes := bytes, pos := 8715, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[83]!).childBody false).drop 8, .end), { bytes := bytes, pos := 8846, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_83_t_tail0 :
    instructionSequenceAt 3272 true { bytes := bytes, pos := 8702, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[83]!).childBody false).drop 0, .end), { bytes := bytes, pos := 8846, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_137_t_tail0 :
    instructionSequenceAt 3218 false { bytes := bytes, pos := 8998, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[137]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9160, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_141_t_tail8 :
    instructionSequenceAt 3206 true { bytes := bytes, pos := 9180, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[141]!).childBody false).drop 8, .end), { bytes := bytes, pos := 9311, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_141_t_tail0 :
    instructionSequenceAt 3214 true { bytes := bytes, pos := 9167, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[141]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9311, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_192_t_tail0 :
    instructionSequenceAt 3163 false { bytes := bytes, pos := 9490, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[192]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9652, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_196_t_tail8 :
    instructionSequenceAt 3151 true { bytes := bytes, pos := 9672, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[196]!).childBody false).drop 8, .end), { bytes := bytes, pos := 9803, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_196_t_tail0 :
    instructionSequenceAt 3159 true { bytes := bytes, pos := 9659, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false)[196]!).childBody false).drop 0, .end), { bytes := bytes, pos := 9803, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_34_t_tail0 :
    instructionSequenceAt 3321 false { bytes := bytes, pos := 10086, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[34]!).childBody false).drop 0, .end), { bytes := bytes, pos := 10248, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_38_t_tail8 :
    instructionSequenceAt 3309 true { bytes := bytes, pos := 10268, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[38]!).childBody false).drop 8, .end), { bytes := bytes, pos := 10399, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_38_t_tail0 :
    instructionSequenceAt 3317 true { bytes := bytes, pos := 10255, limit := 10494 } =
      .ok ((((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true)[38]!).childBody false).drop 0, .end), { bytes := bytes, pos := 10399, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_24_t_tail0 :
    instructionSequenceAt 3340 false { bytes := bytes, pos := 7194, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7356, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_28_t_tail8 :
    instructionSequenceAt 3328 true { bytes := bytes, pos := 7376, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := bytes, pos := 7507, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_28_t_tail0 :
    instructionSequenceAt 3336 true { bytes := bytes, pos := 7363, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7507, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_93_t_tail0 :
    instructionSequenceAt 3271 false { bytes := bytes, pos := 7629, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[93]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7791, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_97_t_tail8 :
    instructionSequenceAt 3259 true { bytes := bytes, pos := 7811, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[97]!).childBody false).drop 8, .end), { bytes := bytes, pos := 7942, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_97_t_tail0 :
    instructionSequenceAt 3267 true { bytes := bytes, pos := 7798, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody false)[97]!).childBody false).drop 0, .end), { bytes := bytes, pos := 7942, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail222 :
    instructionSequenceAt 3135 true { bytes := bytes, pos := 9887, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 222, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail196 :
    instructionSequenceAt 3161 true { bytes := bytes, pos := 9657, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 196, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail192 :
    instructionSequenceAt 3165 true { bytes := bytes, pos := 9488, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 192, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail150 :
    instructionSequenceAt 3207 true { bytes := bytes, pos := 9326, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 150, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail141 :
    instructionSequenceAt 3216 true { bytes := bytes, pos := 9165, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 141, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail137 :
    instructionSequenceAt 3220 true { bytes := bytes, pos := 8996, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 137, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail92 :
    instructionSequenceAt 3265 true { bytes := bytes, pos := 8861, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 92, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail83 :
    instructionSequenceAt 3274 true { bytes := bytes, pos := 8700, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 83, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail79 :
    instructionSequenceAt 3278 true { bytes := bytes, pos := 8531, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 79, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail28 :
    instructionSequenceAt 3329 true { bytes := bytes, pos := 8289, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 28, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail24 :
    instructionSequenceAt 3333 true { bytes := bytes, pos := 8120, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 24, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_t_tail0 :
    instructionSequenceAt 3357 true { bytes := bytes, pos := 8074, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 10016, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_tail38 :
    instructionSequenceAt 3319 false { bytes := bytes, pos := 10253, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true).drop 38, .end), { bytes := bytes, pos := 10486, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_tail34 :
    instructionSequenceAt 3323 false { bytes := bytes, pos := 10084, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true).drop 34, .end), { bytes := bytes, pos := 10486, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_7_e_tail0 :
    instructionSequenceAt 3357 false { bytes := bytes, pos := 10016, limit := 10494 } =
      .ok ((((((((raw.core.codes[6]!).body)[10]!).childBody true)[7]!).childBody true).drop 0, .end), { bytes := bytes, pos := 10486, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail97 :
    instructionSequenceAt 3269 true { bytes := bytes, pos := 7796, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 97, .otherwise), { bytes := bytes, pos := 8055, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail93 :
    instructionSequenceAt 3273 true { bytes := bytes, pos := 7627, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 93, .otherwise), { bytes := bytes, pos := 8055, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail28 :
    instructionSequenceAt 3338 true { bytes := bytes, pos := 7361, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 28, .otherwise), { bytes := bytes, pos := 8055, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail24 :
    instructionSequenceAt 3342 true { bytes := bytes, pos := 7192, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 24, .otherwise), { bytes := bytes, pos := 8055, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_t_tail0 :
    instructionSequenceAt 3366 true { bytes := bytes, pos := 7146, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 8055, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_tail7 :
    instructionSequenceAt 3359 false { bytes := bytes, pos := 8072, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody true).drop 7, .end), { bytes := bytes, pos := 10487, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_10_e_tail0 :
    instructionSequenceAt 3366 false { bytes := bytes, pos := 8055, limit := 10494 } =
      .ok ((((((raw.core.codes[6]!).body)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 10487, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail10 :
    instructionSequenceAt 3368 false { bytes := bytes, pos := 7144, limit := 10494 } =
      .ok ((((raw.core.codes[6]!).body).drop 10, .end), { bytes := bytes, pos := 10494, limit := 10494 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 3378 false { bytes := bytes, pos := 7116, limit := 10494 } =
      .ok ((((raw.core.codes[6]!).body).drop 0, .end), { bytes := bytes, pos := 10494, limit := 10494 }) := by
  cbv

theorem code6_decoded :
    code { bytes := bytes, pos := 7111, limit := 16469 } = .ok (raw.core.codes[6]!, { bytes := bytes, pos := 10494, limit := 16469 }) := by
  refine code_eq_of_parts (size := 3381)
    (payload := { bytes := bytes, pos := 7113, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 7116, limit := 10494 })
    (bodyFinish := { bytes := bytes, pos := 10494, limit := 10494 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.RunningSum.Artifact
