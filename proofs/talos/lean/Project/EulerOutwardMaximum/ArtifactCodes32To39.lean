import Project.EulerOutwardMaximum.ArtifactByteLookup
import Project.EulerOutwardMaximum.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardMaximum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3323, limit := 3438 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3438, limit := 3438 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3319, limit := 5260 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3438, limit := 5260 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3320, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 3323, limit := 3438 })
    (bodyFinish := { bytes := artifactBytes, pos := 3438, limit := 3438 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail1_decoded :
    instructionSequenceAt 128 false { bytes := artifactBytes, pos := 3445, limit := 3572 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 1, .end), { bytes := artifactBytes, pos := 3572, limit := 3572 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3443, limit := 3572 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3572, limit := 3572 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3438, limit := 5260 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 3572, limit := 5260 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 3440, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 3443, limit := 3572 })
    (bodyFinish := { bytes := artifactBytes, pos := 3572, limit := 3572 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail30_decoded :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 3779, limit := 3784 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 30, .end), { bytes := artifactBytes, pos := 3784, limit := 3784 }) := by
  cbv

@[cbv_eval] theorem code34_seq_34_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 3643, limit := 3784 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 29, .end), { bytes := artifactBytes, pos := 3784, limit := 3784 }) := by
  cbv

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 3577, limit := 3784 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3784, limit := 3784 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 3572, limit := 5260 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 3784, limit := 5260 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 3574, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 3577, limit := 3784 })
    (bodyFinish := { bytes := artifactBytes, pos := 3784, limit := 3784 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 3788, limit := 3895 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3895, limit := 3895 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 3784, limit := 5260 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 3895, limit := 5260 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 3785, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 3788, limit := 3895 })
    (bodyFinish := { bytes := artifactBytes, pos := 3895, limit := 3895 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3899, limit := 4014 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4014, limit := 4014 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 3895, limit := 5260 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4014, limit := 5260 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3896, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 3899, limit := 4014 })
    (bodyFinish := { bytes := artifactBytes, pos := 4014, limit := 4014 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 4132, limit := 4280 } =
      .ok ((((((Cache.raw.codes[37]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 4260, limit := 4280 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 4066, limit := 4280 } =
      .ok ((((((Cache.raw.codes[37]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4260, limit := 4280 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail22_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 4275, limit := 4280 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4280, limit := 4280 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 4064, limit := 4280 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4280, limit := 4280 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 4019, limit := 4280 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4280, limit := 4280 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4014, limit := 5260 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4280, limit := 5260 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 4016, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4019, limit := 4280 })
    (bodyFinish := { bytes := artifactBytes, pos := 4280, limit := 4280 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4284, limit := 4291 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4291, limit := 4291 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4280, limit := 5260 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 4291, limit := 5260 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4281, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4284, limit := 4291 })
    (bodyFinish := { bytes := artifactBytes, pos := 4291, limit := 4291 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4295, limit := 4302 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4302, limit := 4302 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 4291, limit := 5260 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 4302, limit := 5260 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4292, limit := 5260 })
    (bodyStart := { bytes := artifactBytes, pos := 4295, limit := 4302 })
    (bodyFinish := { bytes := artifactBytes, pos := 4302, limit := 4302 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded


end Project.EulerOutwardMaximum.Artifact
