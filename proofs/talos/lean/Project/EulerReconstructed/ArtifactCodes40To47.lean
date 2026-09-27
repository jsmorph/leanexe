import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5734, limit := 5741 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5741, limit := 5741 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 5730, limit := 30726 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 5741, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5731, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5734, limit := 5741 })
    (bodyFinish := { bytes := artifactBytes, pos := 5741, limit := 5741 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5745, limit := 5752 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5752, limit := 5752 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 5741, limit := 30726 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5752, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5742, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5745, limit := 5752 })
    (bodyFinish := { bytes := artifactBytes, pos := 5752, limit := 5752 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 5756, limit := 5763 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5763, limit := 5763 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 5752, limit := 30726 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5763, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 5753, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5756, limit := 5763 })
    (bodyFinish := { bytes := artifactBytes, pos := 5763, limit := 5763 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 103 false { bytes := artifactBytes, pos := 5767, limit := 5870 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5870, limit := 5870 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 5763, limit := 30726 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5870, limit := 30726 }) := by
  refine code_eq_of_parts (size := 106)
    (payload := { bytes := artifactBytes, pos := 5764, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5767, limit := 5870 })
    (bodyFinish := { bytes := artifactBytes, pos := 5870, limit := 5870 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 5874, limit := 5899 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5899, limit := 5899 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 5870, limit := 30726 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5899, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 5871, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5874, limit := 5899 })
    (bodyFinish := { bytes := artifactBytes, pos := 5899, limit := 5899 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded

@[cbv_eval] theorem code45_seq_45_tail0_decoded :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 5903, limit := 5976 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5976, limit := 5976 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 5899, limit := 30726 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 5976, limit := 30726 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 5900, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5903, limit := 5976 })
    (bodyFinish := { bytes := artifactBytes, pos := 5976, limit := 5976 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code45_seq_45_tail0_decoded
  · rfl

#print axioms code45_decoded

@[cbv_eval] theorem code46_seq_46_25_t_0_t_tail76_decoded :
    instructionSequenceAt 224 false { bytes := artifactBytes, pos := 6167, limit := 6310 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[25]!).childBody false)[0]!).childBody false).drop 76, .end), { bytes := artifactBytes, pos := 6296, limit := 6310 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_25_t_0_t_tail0_decoded :
    instructionSequenceAt 300 false { bytes := artifactBytes, pos := 6040, limit := 6310 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[25]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6296, limit := 6310 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_25_t_tail0_decoded :
    instructionSequenceAt 302 false { bytes := artifactBytes, pos := 6038, limit := 6310 } =
      .ok ((((((Cache.raw.codes[46]!).body)[25]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6297, limit := 6310 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail25_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 6036, limit := 6310 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 25, .end), { bytes := artifactBytes, pos := 6310, limit := 6310 }) := by
  cbv

@[cbv_eval] theorem code46_seq_46_tail0_decoded :
    instructionSequenceAt 329 false { bytes := artifactBytes, pos := 5981, limit := 6310 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6310, limit := 6310 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 5976, limit := 30726 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 6310, limit := 30726 }) := by
  refine code_eq_of_parts (size := 332)
    (payload := { bytes := artifactBytes, pos := 5978, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 5981, limit := 6310 })
    (bodyFinish := { bytes := artifactBytes, pos := 6310, limit := 6310 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code46_seq_46_tail0_decoded
  · rfl

#print axioms code46_decoded

@[cbv_eval] theorem code47_seq_47_7_e_tail3_decoded :
    instructionSequenceAt 192 false { bytes := artifactBytes, pos := 6344, limit := 6519 } =
      .ok ((((((Cache.raw.codes[47]!).body)[7]!).childBody true).drop 3, .end), { bytes := artifactBytes, pos := 6516, limit := 6519 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_7_e_tail0_decoded :
    instructionSequenceAt 195 false { bytes := artifactBytes, pos := 6339, limit := 6519 } =
      .ok ((((((Cache.raw.codes[47]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 6516, limit := 6519 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_tail7_decoded :
    instructionSequenceAt 197 false { bytes := artifactBytes, pos := 6332, limit := 6519 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 7, .end), { bytes := artifactBytes, pos := 6519, limit := 6519 }) := by
  cbv

@[cbv_eval] theorem code47_seq_47_tail0_decoded :
    instructionSequenceAt 204 false { bytes := artifactBytes, pos := 6315, limit := 6519 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6519, limit := 6519 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 6310, limit := 30726 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 6519, limit := 30726 }) := by
  refine code_eq_of_parts (size := 207)
    (payload := { bytes := artifactBytes, pos := 6312, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 6315, limit := 6519 })
    (bodyFinish := { bytes := artifactBytes, pos := 6519, limit := 6519 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code47_seq_47_tail0_decoded
  · rfl

#print axioms code47_decoded


end Project.EulerReconstructed.Artifact
