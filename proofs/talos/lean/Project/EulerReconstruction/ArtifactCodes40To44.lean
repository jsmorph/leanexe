import Project.EulerReconstruction.ArtifactByteLookup
import Project.EulerReconstruction.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerReconstruction.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_25_t_62_t_tail1_decoded :
    instructionSequenceAt 448 true { bytes := artifactBytes, pos := 4513, limit := 4790 } =
      .ok ((((((((Cache.raw.codes[40]!).body)[25]!).childBody false)[62]!).childBody false).drop 1, .otherwise), { bytes := artifactBytes, pos := 4642, limit := 4790 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_25_t_62_t_tail0_decoded :
    instructionSequenceAt 449 true { bytes := artifactBytes, pos := 4511, limit := 4790 } =
      .ok ((((((((Cache.raw.codes[40]!).body)[25]!).childBody false)[62]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4642, limit := 4790 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_25_t_tail62_decoded :
    instructionSequenceAt 451 true { bytes := artifactBytes, pos := 4509, limit := 4790 } =
      .ok ((((((Cache.raw.codes[40]!).body)[25]!).childBody false).drop 62, .otherwise), { bytes := artifactBytes, pos := 4706, limit := 4790 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_25_t_tail2_decoded :
    instructionSequenceAt 511 true { bytes := artifactBytes, pos := 4381, limit := 4790 } =
      .ok ((((((Cache.raw.codes[40]!).body)[25]!).childBody false).drop 2, .otherwise), { bytes := artifactBytes, pos := 4706, limit := 4790 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_25_t_tail0_decoded :
    instructionSequenceAt 513 true { bytes := artifactBytes, pos := 4377, limit := 4790 } =
      .ok ((((((Cache.raw.codes[40]!).body)[25]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4706, limit := 4790 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_tail25_decoded :
    instructionSequenceAt 515 false { bytes := artifactBytes, pos := 4375, limit := 4790 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 25, .end), { bytes := artifactBytes, pos := 4790, limit := 4790 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 540 false { bytes := artifactBytes, pos := 4250, limit := 4790 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4790, limit := 4790 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 4245, limit := 5619 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 4790, limit := 5619 }) := by
  refine code_eq_of_parts (size := 543)
    (payload := { bytes := artifactBytes, pos := 4247, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 4250, limit := 4790 })
    (bodyFinish := { bytes := artifactBytes, pos := 4790, limit := 4790 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

@[cbv_eval] theorem code41_seq_41_18_t_0_t_tail18_decoded :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 4867, limit := 5157 } =
      .ok ((((((((Cache.raw.codes[41]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 4995, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_18_t_0_t_tail0_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 4836, limit := 5157 } =
      .ok ((((((((Cache.raw.codes[41]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4995, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_18_t_tail0_decoded :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 4834, limit := 5157 } =
      .ok ((((((Cache.raw.codes[41]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4996, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_22_t_tail8_decoded :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 5016, limit := 5157 } =
      .ok ((((((Cache.raw.codes[41]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 5147, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_22_t_tail0_decoded :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 5003, limit := 5157 } =
      .ok ((((((Cache.raw.codes[41]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 5147, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_tail22_decoded :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 5001, limit := 5157 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 22, .end), { bytes := artifactBytes, pos := 5157, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_tail18_decoded :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 4832, limit := 5157 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 18, .end), { bytes := artifactBytes, pos := 5157, limit := 5157 }) := by
  cbv

@[cbv_eval] theorem code41_seq_41_tail0_decoded :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 4795, limit := 5157 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5157, limit := 5157 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 4790, limit := 5619 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5157, limit := 5619 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 4792, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 4795, limit := 5157 })
    (bodyFinish := { bytes := artifactBytes, pos := 5157, limit := 5157 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code41_seq_41_tail0_decoded
  · rfl

#print axioms code41_decoded

@[cbv_eval] theorem code42_seq_42_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 5159, limit := 5185 } =
      .ok ((((Cache.raw.codes[42]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5185, limit := 5185 }) := by
  cbv

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 5157, limit := 5619 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5185, limit := 5619 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 5158, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 5159, limit := 5185 })
    (bodyFinish := { bytes := artifactBytes, pos := 5185, limit := 5185 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code42_seq_42_tail0_decoded
  · rfl

#print axioms code42_decoded

@[cbv_eval] theorem code43_seq_43_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 5189, limit := 5266 } =
      .ok ((((Cache.raw.codes[43]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5266, limit := 5266 }) := by
  cbv

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 5185, limit := 5619 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5266, limit := 5619 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 5186, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 5189, limit := 5266 })
    (bodyFinish := { bytes := artifactBytes, pos := 5266, limit := 5266 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code43_seq_43_tail0_decoded
  · rfl

#print axioms code43_decoded

@[cbv_eval] theorem code44_seq_44_tail43_decoded :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 5459, limit := 5619 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 43, .end), { bytes := artifactBytes, pos := 5619, limit := 5619 }) := by
  cbv

@[cbv_eval] theorem code44_seq_44_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 5330, limit := 5619 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 25, .end), { bytes := artifactBytes, pos := 5619, limit := 5619 }) := by
  cbv

@[cbv_eval] theorem code44_seq_44_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 5271, limit := 5619 } =
      .ok ((((Cache.raw.codes[44]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5619, limit := 5619 }) := by
  cbv

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 5266, limit := 5619 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5619, limit := 5619 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 5268, limit := 5619 })
    (bodyStart := { bytes := artifactBytes, pos := 5271, limit := 5619 })
    (bodyFinish := { bytes := artifactBytes, pos := 5619, limit := 5619 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code44_seq_44_tail0_decoded
  · rfl

#print axioms code44_decoded


end Project.EulerReconstruction.Artifact
