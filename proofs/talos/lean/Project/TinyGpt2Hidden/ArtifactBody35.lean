import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_19_t_tail1 :
    instructionSequenceAt 116 true { bytes := artifactBytes, pos := 4687, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true)[19]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 4688, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_19_t_tail0 :
    instructionSequenceAt 117 true { bytes := artifactBytes, pos := 4686, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true)[19]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4688, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_19_e_tail1 :
    instructionSequenceAt 116 false { bytes := artifactBytes, pos := 4690, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true)[19]!) true).drop 1, .end), { bytes := artifactBytes, pos := 4691, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_19_e_tail0 :
    instructionSequenceAt 117 false { bytes := artifactBytes, pos := 4688, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true)[19]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4691, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_4_t_tail3 :
    instructionSequenceAt 141 true { bytes := artifactBytes, pos := 4608, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[4]!) false).drop 3, .otherwise), { bytes := artifactBytes, pos := 4609, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_4_t_tail0 :
    instructionSequenceAt 144 true { bytes := artifactBytes, pos := 4603, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[4]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4609, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_4_e_tail1 :
    instructionSequenceAt 143 false { bytes := artifactBytes, pos := 4611, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[4]!) true).drop 1, .end), { bytes := artifactBytes, pos := 4612, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_4_e_tail0 :
    instructionSequenceAt 144 false { bytes := artifactBytes, pos := 4609, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[4]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4612, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_t_tail6 :
    instructionSequenceAt 132 true { bytes := artifactBytes, pos := 4643, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) false).drop 6, .otherwise), { bytes := artifactBytes, pos := 4644, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_t_tail0 :
    instructionSequenceAt 138 true { bytes := artifactBytes, pos := 4631, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4644, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_tail33 :
    instructionSequenceAt 105 false { bytes := artifactBytes, pos := 4716, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true).drop 33, .end), { bytes := artifactBytes, pos := 4717, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_tail32 :
    instructionSequenceAt 106 false { bytes := artifactBytes, pos := 4714, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true).drop 32, .end), { bytes := artifactBytes, pos := 4717, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_tail24 :
    instructionSequenceAt 114 false { bytes := artifactBytes, pos := 4699, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true).drop 24, .end), { bytes := artifactBytes, pos := 4717, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_tail16 :
    instructionSequenceAt 122 false { bytes := artifactBytes, pos := 4679, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true).drop 16, .end), { bytes := artifactBytes, pos := 4717, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_tail8 :
    instructionSequenceAt 130 false { bytes := artifactBytes, pos := 4664, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true).drop 8, .end), { bytes := artifactBytes, pos := 4717, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_10_e_tail0 :
    instructionSequenceAt 138 false { bytes := artifactBytes, pos := 4644, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false)[10]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4717, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_tail12 :
    instructionSequenceAt 138 false { bytes := artifactBytes, pos := 4719, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false).drop 12, .end), { bytes := artifactBytes, pos := 4720, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_tail8 :
    instructionSequenceAt 142 false { bytes := artifactBytes, pos := 4617, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false).drop 8, .end), { bytes := artifactBytes, pos := 4720, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_0_t_tail0 :
    instructionSequenceAt 150 false { bytes := artifactBytes, pos := 4595, limit := 4743 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false)[0]!) false).drop 0, .end), { bytes := artifactBytes, pos := 4720, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_tail1 :
    instructionSequenceAt 151 false { bytes := artifactBytes, pos := 4720, limit := 4743 } =
      .ok (((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false).drop 1, .end), { bytes := artifactBytes, pos := 4721, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_2_t_tail0 :
    instructionSequenceAt 152 false { bytes := artifactBytes, pos := 4593, limit := 4743 } =
      .ok (((Instr.childBody ((Cache.raw.codes[35]!.body)[2]!) false).drop 0, .end), { bytes := artifactBytes, pos := 4721, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_6_t_tail4 :
    instructionSequenceAt 144 true { bytes := artifactBytes, pos := 4736, limit := 4743 } =
      .ok (((Instr.childBody ((Cache.raw.codes[35]!.body)[6]!) false).drop 4, .otherwise), { bytes := artifactBytes, pos := 4737, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_6_t_tail0 :
    instructionSequenceAt 148 true { bytes := artifactBytes, pos := 4728, limit := 4743 } =
      .ok (((Instr.childBody ((Cache.raw.codes[35]!.body)[6]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4737, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_6_e_tail0 :
    instructionSequenceAt 148 false { bytes := artifactBytes, pos := 4737, limit := 4743 } =
      .ok (((Instr.childBody ((Cache.raw.codes[35]!.body)[6]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4738, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_tail9 :
    instructionSequenceAt 147 false { bytes := artifactBytes, pos := 4742, limit := 4743 } =
      .ok (((Cache.raw.codes[35]!.body).drop 9, .end), { bytes := artifactBytes, pos := 4743, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_tail8 :
    instructionSequenceAt 148 false { bytes := artifactBytes, pos := 4740, limit := 4743 } =
      .ok (((Cache.raw.codes[35]!.body).drop 8, .end), { bytes := artifactBytes, pos := 4743, limit := 4743 }) := by cbv

@[cbv_eval] theorem sequence35_tail0 :
    instructionSequenceAt 156 false { bytes := artifactBytes, pos := 4587, limit := 4743 } =
      .ok (((Cache.raw.codes[35]!.body).drop 0, .end), { bytes := artifactBytes, pos := 4743, limit := 4743 }) := by cbv

theorem code35_decoded_parts :
    code { bytes := artifactBytes, pos := 4582, limit := 16006 } = .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 4743, limit := 16006 }) := by
  refine code_eq_of_parts (size := 159)
    (payload := { bytes := artifactBytes, pos := 4584, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 4587, limit := 4743 })
    (bodyFinish := { bytes := artifactBytes, pos := 4743, limit := 4743 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence35_tail0
  · rfl

#print axioms code35_decoded_parts
end Project.TinyGpt2Hidden.Artifact
