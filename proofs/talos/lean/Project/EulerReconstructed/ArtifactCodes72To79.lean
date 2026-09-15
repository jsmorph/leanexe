import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code72_seq_72_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 10732, limit := 10739 } =
      .ok ((((Cache.raw.codes[72]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10739, limit := 10739 }) := by
  cbv

theorem code72_decoded :
    code { bytes := artifactBytes, pos := 10728, limit := 30726 } =
      .ok (Cache.raw.codes[72]!, { bytes := artifactBytes, pos := 10739, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 10729, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 10732, limit := 10739 })
    (bodyFinish := { bytes := artifactBytes, pos := 10739, limit := 10739 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code72_seq_72_tail0_decoded
  · rfl

#print axioms code72_decoded

@[cbv_eval] theorem code73_seq_73_2_t_0_t_75_e_tail1_decoded :
    instructionSequenceAt 385 false { bytes := artifactBytes, pos := 10965, limit := 11213 } =
      .ok ((((((((((Cache.raw.codes[73]!).body)[2]!).childBody false)[0]!).childBody false)[75]!).childBody true).drop 1, .end), { bytes := artifactBytes, pos := 11093, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_2_t_0_t_75_e_tail0_decoded :
    instructionSequenceAt 386 false { bytes := artifactBytes, pos := 10963, limit := 11213 } =
      .ok ((((((((((Cache.raw.codes[73]!).body)[2]!).childBody false)[0]!).childBody false)[75]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 11093, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_2_t_0_t_tail75_decoded :
    instructionSequenceAt 388 false { bytes := artifactBytes, pos := 10916, limit := 11213 } =
      .ok ((((((((Cache.raw.codes[73]!).body)[2]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := artifactBytes, pos := 11096, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_2_t_0_t_tail15_decoded :
    instructionSequenceAt 448 false { bytes := artifactBytes, pos := 10788, limit := 11213 } =
      .ok ((((((((Cache.raw.codes[73]!).body)[2]!).childBody false)[0]!).childBody false).drop 15, .end), { bytes := artifactBytes, pos := 11096, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_2_t_0_t_tail0_decoded :
    instructionSequenceAt 463 false { bytes := artifactBytes, pos := 10752, limit := 11213 } =
      .ok ((((((((Cache.raw.codes[73]!).body)[2]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11096, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_2_t_tail0_decoded :
    instructionSequenceAt 465 false { bytes := artifactBytes, pos := 10750, limit := 11213 } =
      .ok ((((((Cache.raw.codes[73]!).body)[2]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11097, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_tail2_decoded :
    instructionSequenceAt 467 false { bytes := artifactBytes, pos := 10748, limit := 11213 } =
      .ok ((((Cache.raw.codes[73]!).body).drop 2, .end), { bytes := artifactBytes, pos := 11213, limit := 11213 }) := by
  cbv

@[cbv_eval] theorem code73_seq_73_tail0_decoded :
    instructionSequenceAt 469 false { bytes := artifactBytes, pos := 10744, limit := 11213 } =
      .ok ((((Cache.raw.codes[73]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11213, limit := 11213 }) := by
  cbv

theorem code73_decoded :
    code { bytes := artifactBytes, pos := 10739, limit := 30726 } =
      .ok (Cache.raw.codes[73]!, { bytes := artifactBytes, pos := 11213, limit := 30726 }) := by
  refine code_eq_of_parts (size := 472)
    (payload := { bytes := artifactBytes, pos := 10741, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 10744, limit := 11213 })
    (bodyFinish := { bytes := artifactBytes, pos := 11213, limit := 11213 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code73_seq_73_tail0_decoded
  · rfl

#print axioms code73_decoded

@[cbv_eval] theorem code74_seq_74_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 11217, limit := 11242 } =
      .ok ((((Cache.raw.codes[74]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11242, limit := 11242 }) := by
  cbv

theorem code74_decoded :
    code { bytes := artifactBytes, pos := 11213, limit := 30726 } =
      .ok (Cache.raw.codes[74]!, { bytes := artifactBytes, pos := 11242, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 11214, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 11217, limit := 11242 })
    (bodyFinish := { bytes := artifactBytes, pos := 11242, limit := 11242 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code74_seq_74_tail0_decoded
  · rfl

#print axioms code74_decoded

@[cbv_eval] theorem code75_seq_75_25_t_62_t_tail1_decoded :
    instructionSequenceAt 448 true { bytes := artifactBytes, pos := 11510, limit := 11787 } =
      .ok ((((((((Cache.raw.codes[75]!).body)[25]!).childBody false)[62]!).childBody false).drop 1, .otherwise), { bytes := artifactBytes, pos := 11639, limit := 11787 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_25_t_62_t_tail0_decoded :
    instructionSequenceAt 449 true { bytes := artifactBytes, pos := 11508, limit := 11787 } =
      .ok ((((((((Cache.raw.codes[75]!).body)[25]!).childBody false)[62]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 11639, limit := 11787 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_25_t_tail62_decoded :
    instructionSequenceAt 451 true { bytes := artifactBytes, pos := 11506, limit := 11787 } =
      .ok ((((((Cache.raw.codes[75]!).body)[25]!).childBody false).drop 62, .otherwise), { bytes := artifactBytes, pos := 11703, limit := 11787 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_25_t_tail2_decoded :
    instructionSequenceAt 511 true { bytes := artifactBytes, pos := 11378, limit := 11787 } =
      .ok ((((((Cache.raw.codes[75]!).body)[25]!).childBody false).drop 2, .otherwise), { bytes := artifactBytes, pos := 11703, limit := 11787 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_25_t_tail0_decoded :
    instructionSequenceAt 513 true { bytes := artifactBytes, pos := 11374, limit := 11787 } =
      .ok ((((((Cache.raw.codes[75]!).body)[25]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 11703, limit := 11787 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_tail25_decoded :
    instructionSequenceAt 515 false { bytes := artifactBytes, pos := 11372, limit := 11787 } =
      .ok ((((Cache.raw.codes[75]!).body).drop 25, .end), { bytes := artifactBytes, pos := 11787, limit := 11787 }) := by
  cbv

@[cbv_eval] theorem code75_seq_75_tail0_decoded :
    instructionSequenceAt 540 false { bytes := artifactBytes, pos := 11247, limit := 11787 } =
      .ok ((((Cache.raw.codes[75]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11787, limit := 11787 }) := by
  cbv

theorem code75_decoded :
    code { bytes := artifactBytes, pos := 11242, limit := 30726 } =
      .ok (Cache.raw.codes[75]!, { bytes := artifactBytes, pos := 11787, limit := 30726 }) := by
  refine code_eq_of_parts (size := 543)
    (payload := { bytes := artifactBytes, pos := 11244, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 11247, limit := 11787 })
    (bodyFinish := { bytes := artifactBytes, pos := 11787, limit := 11787 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code75_seq_75_tail0_decoded
  · rfl

#print axioms code75_decoded

@[cbv_eval] theorem code76_seq_76_tail0_decoded :
    instructionSequenceAt 49 false { bytes := artifactBytes, pos := 11791, limit := 11840 } =
      .ok ((((Cache.raw.codes[76]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11840, limit := 11840 }) := by
  cbv

theorem code76_decoded :
    code { bytes := artifactBytes, pos := 11787, limit := 30726 } =
      .ok (Cache.raw.codes[76]!, { bytes := artifactBytes, pos := 11840, limit := 30726 }) := by
  refine code_eq_of_parts (size := 52)
    (payload := { bytes := artifactBytes, pos := 11788, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 11791, limit := 11840 })
    (bodyFinish := { bytes := artifactBytes, pos := 11840, limit := 11840 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code76_seq_76_tail0_decoded
  · rfl

#print axioms code76_decoded

@[cbv_eval] theorem code77_seq_77_29_t_69_t_tail45_decoded :
    instructionSequenceAt 516 true { bytes := artifactBytes, pos := 12260, limit := 12508 } =
      .ok ((((((((Cache.raw.codes[77]!).body)[29]!).childBody false)[69]!).childBody false).drop 45, .otherwise), { bytes := artifactBytes, pos := 12388, limit := 12508 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_29_t_69_t_tail0_decoded :
    instructionSequenceAt 561 true { bytes := artifactBytes, pos := 12136, limit := 12508 } =
      .ok ((((((((Cache.raw.codes[77]!).body)[29]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12388, limit := 12508 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_29_t_tail69_decoded :
    instructionSequenceAt 563 true { bytes := artifactBytes, pos := 12134, limit := 12508 } =
      .ok ((((((Cache.raw.codes[77]!).body)[29]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 12440, limit := 12508 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_29_t_tail56_decoded :
    instructionSequenceAt 576 true { bytes := artifactBytes, pos := 12003, limit := 12508 } =
      .ok ((((((Cache.raw.codes[77]!).body)[29]!).childBody false).drop 56, .otherwise), { bytes := artifactBytes, pos := 12440, limit := 12508 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_29_t_tail0_decoded :
    instructionSequenceAt 632 true { bytes := artifactBytes, pos := 11913, limit := 12508 } =
      .ok ((((((Cache.raw.codes[77]!).body)[29]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12440, limit := 12508 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_tail29_decoded :
    instructionSequenceAt 634 false { bytes := artifactBytes, pos := 11911, limit := 12508 } =
      .ok ((((Cache.raw.codes[77]!).body).drop 29, .end), { bytes := artifactBytes, pos := 12508, limit := 12508 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_tail0_decoded :
    instructionSequenceAt 663 false { bytes := artifactBytes, pos := 11845, limit := 12508 } =
      .ok ((((Cache.raw.codes[77]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12508, limit := 12508 }) := by
  cbv

theorem code77_decoded :
    code { bytes := artifactBytes, pos := 11840, limit := 30726 } =
      .ok (Cache.raw.codes[77]!, { bytes := artifactBytes, pos := 12508, limit := 30726 }) := by
  refine code_eq_of_parts (size := 666)
    (payload := { bytes := artifactBytes, pos := 11842, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 11845, limit := 12508 })
    (bodyFinish := { bytes := artifactBytes, pos := 12508, limit := 12508 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code77_seq_77_tail0_decoded
  · rfl

#print axioms code77_decoded

@[cbv_eval] theorem code78_seq_78_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 12512, limit := 12519 } =
      .ok ((((Cache.raw.codes[78]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12519, limit := 12519 }) := by
  cbv

theorem code78_decoded :
    code { bytes := artifactBytes, pos := 12508, limit := 30726 } =
      .ok (Cache.raw.codes[78]!, { bytes := artifactBytes, pos := 12519, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 12509, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12512, limit := 12519 })
    (bodyFinish := { bytes := artifactBytes, pos := 12519, limit := 12519 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code78_seq_78_tail0_decoded
  · rfl

#print axioms code78_decoded

@[cbv_eval] theorem code79_seq_79_tail0_decoded :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 12523, limit := 12530 } =
      .ok ((((Cache.raw.codes[79]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12530, limit := 12530 }) := by
  cbv

theorem code79_decoded :
    code { bytes := artifactBytes, pos := 12519, limit := 30726 } =
      .ok (Cache.raw.codes[79]!, { bytes := artifactBytes, pos := 12530, limit := 30726 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 12520, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 12523, limit := 12530 })
    (bodyFinish := { bytes := artifactBytes, pos := 12530, limit := 12530 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code79_seq_79_tail0_decoded
  · rfl

#print axioms code79_decoded


end Project.EulerReconstructed.Artifact
