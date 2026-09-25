import Project.RunningSum.ArtifactByteLookup
import Project.RunningSum.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.RunningSum.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_34_t_0_t_tail23 :
    instructionSequenceAt 3662 false { bytes := bytes, pos := 12545, limit := 14877 } =
      .ok ((((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 23, .end), { bytes := bytes, pos := 12680, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_34_t_0_t_tail0 :
    instructionSequenceAt 3685 false { bytes := bytes, pos := 12496, limit := 14877 } =
      .ok ((((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true)[34]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 12680, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_34_t_tail0 :
    instructionSequenceAt 3687 false { bytes := bytes, pos := 12494, limit := 14877 } =
      .ok ((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true)[34]!).childBody false).drop 0, .end), { bytes := bytes, pos := 12681, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_38_t_tail14 :
    instructionSequenceAt 3669 true { bytes := bytes, pos := 12719, limit := 14877 } =
      .ok ((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true)[38]!).childBody false).drop 14, .end), { bytes := bytes, pos := 12848, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_38_t_tail0 :
    instructionSequenceAt 3683 true { bytes := bytes, pos := 12689, limit := 14877 } =
      .ok ((((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true)[38]!).childBody false).drop 0, .end), { bytes := bytes, pos := 12848, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_t_tail57 :
    instructionSequenceAt 3666 true { bytes := bytes, pos := 12249, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody false).drop 57, .otherwise), { bytes := bytes, pos := 12406, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_t_tail43 :
    instructionSequenceAt 3680 true { bytes := bytes, pos := 12022, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody false).drop 43, .otherwise), { bytes := bytes, pos := 12406, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_t_tail0 :
    instructionSequenceAt 3723 true { bytes := bytes, pos := 11937, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 12406, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_tail114 :
    instructionSequenceAt 3609 false { bytes := bytes, pos := 13092, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true).drop 114, .end), { bytes := bytes, pos := 13262, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_tail68 :
    instructionSequenceAt 3655 false { bytes := bytes, pos := 12962, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true).drop 68, .end), { bytes := bytes, pos := 13262, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_tail38 :
    instructionSequenceAt 3685 false { bytes := bytes, pos := 12687, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true).drop 38, .end), { bytes := bytes, pos := 13262, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_tail34 :
    instructionSequenceAt 3689 false { bytes := bytes, pos := 12492, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true).drop 34, .end), { bytes := bytes, pos := 13262, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_63_e_tail0 :
    instructionSequenceAt 3723 false { bytes := bytes, pos := 12406, limit := 14877 } =
      .ok ((((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false)[63]!).childBody true).drop 0, .end), { bytes := bytes, pos := 13262, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_tail147 :
    instructionSequenceAt 3641 false { bytes := bytes, pos := 13652, limit := 14877 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 147, .end), { bytes := bytes, pos := 13780, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_tail98 :
    instructionSequenceAt 3690 false { bytes := bytes, pos := 13513, limit := 14877 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 98, .end), { bytes := bytes, pos := 13780, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_tail85 :
    instructionSequenceAt 3703 false { bytes := bytes, pos := 13382, limit := 14877 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 85, .end), { bytes := bytes, pos := 13780, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_tail63 :
    instructionSequenceAt 3725 false { bytes := bytes, pos := 11935, limit := 14877 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 63, .end), { bytes := bytes, pos := 13780, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_tail13 :
    instructionSequenceAt 3775 false { bytes := bytes, pos := 11807, limit := 14877 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 13, .end), { bytes := bytes, pos := 13780, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_0_t_tail0 :
    instructionSequenceAt 3788 false { bytes := bytes, pos := 11777, limit := 14877 } =
      .ok ((((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 13780, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_t_10_e_tail54 :
    instructionSequenceAt 3754 false { bytes := bytes, pos := 11556, limit := 14877 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 54, .end), { bytes := bytes, pos := 11711, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_t_10_e_tail19 :
    instructionSequenceAt 3789 false { bytes := bytes, pos := 11428, limit := 14877 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 19, .end), { bytes := bytes, pos := 11711, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_t_10_e_tail0 :
    instructionSequenceAt 3808 false { bytes := bytes, pos := 11390, limit := 14877 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody false)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 11711, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_28_t_tail0 :
    instructionSequenceAt 3790 false { bytes := bytes, pos := 11775, limit := 14877 } =
      .ok ((((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := bytes, pos := 13781, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_t_tail10 :
    instructionSequenceAt 3810 true { bytes := bytes, pos := 11292, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody false).drop 10, .otherwise), { bytes := bytes, pos := 11712, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_t_tail0 :
    instructionSequenceAt 3820 true { bytes := bytes, pos := 11264, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody false).drop 0, .otherwise), { bytes := bytes, pos := 11712, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_tail103 :
    instructionSequenceAt 3717 false { bytes := bytes, pos := 14074, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true).drop 103, .end), { bytes := bytes, pos := 14203, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_tail87 :
    instructionSequenceAt 3733 false { bytes := bytes, pos := 13945, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true).drop 87, .end), { bytes := bytes, pos := 14203, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_tail43 :
    instructionSequenceAt 3777 false { bytes := bytes, pos := 13816, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true).drop 43, .end), { bytes := bytes, pos := 14203, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_tail28 :
    instructionSequenceAt 3792 false { bytes := bytes, pos := 11773, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true).drop 28, .end), { bytes := bytes, pos := 14203, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_10_e_tail0 :
    instructionSequenceAt 3820 false { bytes := bytes, pos := 11712, limit := 14877 } =
      .ok ((((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true)[10]!).childBody true).drop 0, .end), { bytes := bytes, pos := 14203, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_tail10 :
    instructionSequenceAt 3822 false { bytes := bytes, pos := 11262, limit := 14877 } =
      .ok ((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true).drop 10, .end), { bytes := bytes, pos := 14204, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_59_e_tail0 :
    instructionSequenceAt 3832 false { bytes := bytes, pos := 11234, limit := 14877 } =
      .ok ((((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false)[59]!).childBody true).drop 0, .end), { bytes := bytes, pos := 14204, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail120 :
    instructionSequenceAt 3773 false { bytes := bytes, pos := 14667, limit := 14877 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 120, .end), { bytes := bytes, pos := 14797, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail107 :
    instructionSequenceAt 3786 false { bytes := bytes, pos := 14538, limit := 14877 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 107, .end), { bytes := bytes, pos := 14797, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail91 :
    instructionSequenceAt 3802 false { bytes := bytes, pos := 14410, limit := 14877 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 91, .end), { bytes := bytes, pos := 14797, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail73 :
    instructionSequenceAt 3820 false { bytes := bytes, pos := 14248, limit := 14877 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 73, .end), { bytes := bytes, pos := 14797, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail59 :
    instructionSequenceAt 3834 false { bytes := bytes, pos := 11136, limit := 14877 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 59, .end), { bytes := bytes, pos := 14797, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_0_t_tail0 :
    instructionSequenceAt 3893 false { bytes := bytes, pos := 11016, limit := 14877 } =
      .ok ((((((((raw.core.codes[8]!).body)[32]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := bytes, pos := 14797, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_32_t_tail0 :
    instructionSequenceAt 3895 false { bytes := bytes, pos := 11014, limit := 14877 } =
      .ok ((((((raw.core.codes[8]!).body)[32]!).childBody false).drop 0, .end), { bytes := bytes, pos := 14798, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail32 :
    instructionSequenceAt 3897 false { bytes := bytes, pos := 11012, limit := 14877 } =
      .ok ((((raw.core.codes[8]!).body).drop 32, .end), { bytes := bytes, pos := 14877, limit := 14877 }) := by
  cbv

@[cbv_eval] theorem sequence_8_tail0 :
    instructionSequenceAt 3929 false { bytes := bytes, pos := 10948, limit := 14877 } =
      .ok ((((raw.core.codes[8]!).body).drop 0, .end), { bytes := bytes, pos := 14877, limit := 14877 }) := by
  cbv

theorem code8_decoded :
    code { bytes := bytes, pos := 10942, limit := 16469 } = .ok (raw.core.codes[8]!, { bytes := bytes, pos := 14877, limit := 16469 }) := by
  refine code_eq_of_parts (size := 3933)
    (payload := { bytes := bytes, pos := 10944, limit := 16469 })
    (bodyStart := { bytes := bytes, pos := 10948, limit := 14877 })
    (bodyFinish := { bytes := bytes, pos := 14877, limit := 14877 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.RunningSum.Artifact
