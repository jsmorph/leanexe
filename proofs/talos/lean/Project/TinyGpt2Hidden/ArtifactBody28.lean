import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence28_10_e_10_e_3_t_tail1 :
    instructionSequenceAt 139 true { bytes := artifactBytes, pos := 3923, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3924, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_3_t_tail0 :
    instructionSequenceAt 140 true { bytes := artifactBytes, pos := 3921, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3924, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_3_e_tail1 :
    instructionSequenceAt 139 false { bytes := artifactBytes, pos := 3926, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3927, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_3_e_tail0 :
    instructionSequenceAt 140 false { bytes := artifactBytes, pos := 3924, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3927, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_6_t_tail1 :
    instructionSequenceAt 136 true { bytes := artifactBytes, pos := 3934, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[6]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3935, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_6_t_tail0 :
    instructionSequenceAt 137 true { bytes := artifactBytes, pos := 3932, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[6]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3935, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_6_e_tail1 :
    instructionSequenceAt 136 false { bytes := artifactBytes, pos := 3937, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[6]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3938, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_6_e_tail0 :
    instructionSequenceAt 137 false { bytes := artifactBytes, pos := 3935, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[6]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3938, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_10_t_tail8 :
    instructionSequenceAt 125 true { bytes := artifactBytes, pos := 3960, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[10]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3961, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_10_t_tail0 :
    instructionSequenceAt 133 true { bytes := artifactBytes, pos := 3944, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[10]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3961, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_10_e_tail8 :
    instructionSequenceAt 125 false { bytes := artifactBytes, pos := 3977, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[10]!) true).drop 8, .end), { bytes := artifactBytes, pos := 3978, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_10_e_tail0 :
    instructionSequenceAt 133 false { bytes := artifactBytes, pos := 3961, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true)[10]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3978, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_3_t_tail1 :
    instructionSequenceAt 151 true { bytes := artifactBytes, pos := 3876, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3877, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_3_t_tail0 :
    instructionSequenceAt 152 true { bytes := artifactBytes, pos := 3874, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3877, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_3_e_tail1 :
    instructionSequenceAt 151 false { bytes := artifactBytes, pos := 3879, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3880, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_3_e_tail0 :
    instructionSequenceAt 152 false { bytes := artifactBytes, pos := 3877, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3880, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_6_t_tail1 :
    instructionSequenceAt 148 true { bytes := artifactBytes, pos := 3887, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[6]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3888, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_6_t_tail0 :
    instructionSequenceAt 149 true { bytes := artifactBytes, pos := 3885, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[6]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3888, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_6_e_tail1 :
    instructionSequenceAt 148 false { bytes := artifactBytes, pos := 3890, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[6]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3891, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_6_e_tail0 :
    instructionSequenceAt 149 false { bytes := artifactBytes, pos := 3888, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[6]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3891, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_t_tail8 :
    instructionSequenceAt 137 true { bytes := artifactBytes, pos := 3913, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3914, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_t_tail0 :
    instructionSequenceAt 145 true { bytes := artifactBytes, pos := 3897, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3914, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_tail11 :
    instructionSequenceAt 134 false { bytes := artifactBytes, pos := 3978, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true).drop 11, .end), { bytes := artifactBytes, pos := 3979, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_tail8 :
    instructionSequenceAt 137 false { bytes := artifactBytes, pos := 3940, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true).drop 8, .end), { bytes := artifactBytes, pos := 3979, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_10_e_tail0 :
    instructionSequenceAt 145 false { bytes := artifactBytes, pos := 3914, limit := 3989 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true)[10]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3979, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_3_t_tail1 :
    instructionSequenceAt 163 true { bytes := artifactBytes, pos := 3829, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3830, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_3_t_tail0 :
    instructionSequenceAt 164 true { bytes := artifactBytes, pos := 3827, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3830, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_3_e_tail1 :
    instructionSequenceAt 163 false { bytes := artifactBytes, pos := 3832, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3833, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_3_e_tail0 :
    instructionSequenceAt 164 false { bytes := artifactBytes, pos := 3830, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3833, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_6_t_tail1 :
    instructionSequenceAt 160 true { bytes := artifactBytes, pos := 3840, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[6]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3841, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_6_t_tail0 :
    instructionSequenceAt 161 true { bytes := artifactBytes, pos := 3838, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[6]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3841, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_6_e_tail1 :
    instructionSequenceAt 160 false { bytes := artifactBytes, pos := 3843, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[6]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3844, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_6_e_tail0 :
    instructionSequenceAt 161 false { bytes := artifactBytes, pos := 3841, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[6]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3844, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_t_tail8 :
    instructionSequenceAt 149 true { bytes := artifactBytes, pos := 3866, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3867, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_t_tail0 :
    instructionSequenceAt 157 true { bytes := artifactBytes, pos := 3850, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3867, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_tail11 :
    instructionSequenceAt 146 false { bytes := artifactBytes, pos := 3979, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true).drop 11, .end), { bytes := artifactBytes, pos := 3980, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_tail8 :
    instructionSequenceAt 149 false { bytes := artifactBytes, pos := 3893, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true).drop 8, .end), { bytes := artifactBytes, pos := 3980, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_10_e_tail0 :
    instructionSequenceAt 157 false { bytes := artifactBytes, pos := 3867, limit := 3989 } =
      .ok (((Instr.childBody ((Cache.raw.codes[28]!.body)[10]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3980, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_tail15 :
    instructionSequenceAt 154 false { bytes := artifactBytes, pos := 3988, limit := 3989 } =
      .ok (((Cache.raw.codes[28]!.body).drop 15, .end), { bytes := artifactBytes, pos := 3989, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_tail8 :
    instructionSequenceAt 161 false { bytes := artifactBytes, pos := 3846, limit := 3989 } =
      .ok (((Cache.raw.codes[28]!.body).drop 8, .end), { bytes := artifactBytes, pos := 3989, limit := 3989 }) := by cbv

@[cbv_eval] theorem sequence28_tail0 :
    instructionSequenceAt 169 false { bytes := artifactBytes, pos := 3820, limit := 3989 } =
      .ok (((Cache.raw.codes[28]!.body).drop 0, .end), { bytes := artifactBytes, pos := 3989, limit := 3989 }) := by cbv

theorem code28_decoded_parts :
    code { bytes := artifactBytes, pos := 3815, limit := 16006 } = .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 3989, limit := 16006 }) := by
  refine code_eq_of_parts (size := 172)
    (payload := { bytes := artifactBytes, pos := 3817, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 3820, limit := 3989 })
    (bodyFinish := { bytes := artifactBytes, pos := 3989, limit := 3989 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence28_tail0
  · rfl

#print axioms code28_decoded_parts
end Project.TinyGpt2Hidden.Artifact
