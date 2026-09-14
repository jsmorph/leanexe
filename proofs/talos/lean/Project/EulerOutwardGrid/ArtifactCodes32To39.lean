import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code32_seq_32_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3351, limit := 3466 } =
      .ok ((((Cache.raw.codes[32]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3466, limit := 3466 }) := by
  cbv

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 3347, limit := 5728 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 3466, limit := 5728 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3348, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 3351, limit := 3466 })
    (bodyFinish := { bytes := artifactBytes, pos := 3466, limit := 3466 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code32_seq_32_tail0_decoded
  · rfl

#print axioms code32_decoded

@[cbv_eval] theorem code33_seq_33_tail1_decoded :
    instructionSequenceAt 128 false { bytes := artifactBytes, pos := 3473, limit := 3600 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 1, .end), { bytes := artifactBytes, pos := 3600, limit := 3600 }) := by
  cbv

@[cbv_eval] theorem code33_seq_33_tail0_decoded :
    instructionSequenceAt 129 false { bytes := artifactBytes, pos := 3471, limit := 3600 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3600, limit := 3600 }) := by
  cbv

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 3466, limit := 5728 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 3600, limit := 5728 }) := by
  refine code_eq_of_parts (size := 132)
    (payload := { bytes := artifactBytes, pos := 3468, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 3471, limit := 3600 })
    (bodyFinish := { bytes := artifactBytes, pos := 3600, limit := 3600 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code33_seq_33_tail0_decoded
  · rfl

#print axioms code33_decoded

@[cbv_eval] theorem code34_seq_34_tail30_decoded :
    instructionSequenceAt 177 false { bytes := artifactBytes, pos := 3807, limit := 3812 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 30, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

@[cbv_eval] theorem code34_seq_34_tail29_decoded :
    instructionSequenceAt 178 false { bytes := artifactBytes, pos := 3671, limit := 3812 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 29, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

@[cbv_eval] theorem code34_seq_34_tail0_decoded :
    instructionSequenceAt 207 false { bytes := artifactBytes, pos := 3605, limit := 3812 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3812, limit := 3812 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 3600, limit := 5728 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 3812, limit := 5728 }) := by
  refine code_eq_of_parts (size := 210)
    (payload := { bytes := artifactBytes, pos := 3602, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 3605, limit := 3812 })
    (bodyFinish := { bytes := artifactBytes, pos := 3812, limit := 3812 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code34_seq_34_tail0_decoded
  · rfl

#print axioms code34_decoded

@[cbv_eval] theorem code35_seq_35_tail0_decoded :
    instructionSequenceAt 107 false { bytes := artifactBytes, pos := 3816, limit := 3923 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3923, limit := 3923 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 3812, limit := 5728 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 3923, limit := 5728 }) := by
  refine code_eq_of_parts (size := 110)
    (payload := { bytes := artifactBytes, pos := 3813, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 3816, limit := 3923 })
    (bodyFinish := { bytes := artifactBytes, pos := 3923, limit := 3923 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code35_seq_35_tail0_decoded
  · rfl

#print axioms code35_decoded

@[cbv_eval] theorem code36_seq_36_tail0_decoded :
    instructionSequenceAt 115 false { bytes := artifactBytes, pos := 3927, limit := 4042 } =
      .ok ((((Cache.raw.codes[36]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4042, limit := 4042 }) := by
  cbv

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 3923, limit := 5728 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4042, limit := 5728 }) := by
  refine code_eq_of_parts (size := 118)
    (payload := { bytes := artifactBytes, pos := 3924, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 3927, limit := 4042 })
    (bodyFinish := { bytes := artifactBytes, pos := 4042, limit := 4042 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code36_seq_36_tail0_decoded
  · rfl

#print axioms code36_decoded

@[cbv_eval] theorem code37_seq_37_21_t_tail33_decoded :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 4160, limit := 4308 } =
      .ok ((((((Cache.raw.codes[37]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 4288, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_21_t_tail0_decoded :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 4094, limit := 4308 } =
      .ok ((((((Cache.raw.codes[37]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4288, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail22_decoded :
    instructionSequenceAt 239 false { bytes := artifactBytes, pos := 4303, limit := 4308 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 22, .end), { bytes := artifactBytes, pos := 4308, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail21_decoded :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 4092, limit := 4308 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4308, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem code37_seq_37_tail0_decoded :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 4047, limit := 4308 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4308, limit := 4308 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4042, limit := 5728 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4308, limit := 5728 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 4044, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4047, limit := 4308 })
    (bodyFinish := { bytes := artifactBytes, pos := 4308, limit := 4308 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code37_seq_37_tail0_decoded
  · rfl

#print axioms code37_decoded

@[cbv_eval] theorem code38_seq_38_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4312, limit := 4319 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4319, limit := 4319 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4308, limit := 5728 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 4319, limit := 5728 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4309, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4312, limit := 4319 })
    (bodyFinish := { bytes := artifactBytes, pos := 4319, limit := 4319 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code38_seq_38_tail0_decoded
  · rfl

#print axioms code38_decoded

@[cbv_eval] theorem code39_seq_39_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 4323, limit := 4330 } =
      .ok ((((Cache.raw.codes[39]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4330, limit := 4330 }) := by
  cbv

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 4319, limit := 5728 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 4330, limit := 5728 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 4320, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 4323, limit := 4330 })
    (bodyFinish := { bytes := artifactBytes, pos := 4330, limit := 4330 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code39_seq_39_tail0_decoded
  · rfl

#print axioms code39_decoded


end Project.EulerOutwardGrid.Artifact
