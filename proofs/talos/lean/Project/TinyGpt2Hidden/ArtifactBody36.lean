import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence36_2_t_0_t_4_t_tail3 :
    instructionSequenceAt 58 true { bytes := artifactBytes, pos := 4768, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false)[4]!) false).drop 3, .otherwise), { bytes := artifactBytes, pos := 4769, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_4_t_tail0 :
    instructionSequenceAt 61 true { bytes := artifactBytes, pos := 4763, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false)[4]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4769, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_4_e_tail1 :
    instructionSequenceAt 60 false { bytes := artifactBytes, pos := 4771, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false)[4]!) true).drop 1, .end), { bytes := artifactBytes, pos := 4772, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_4_e_tail0 :
    instructionSequenceAt 61 false { bytes := artifactBytes, pos := 4769, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false)[4]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4772, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_tail23 :
    instructionSequenceAt 44 false { bytes := artifactBytes, pos := 4802, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false).drop 23, .end), { bytes := artifactBytes, pos := 4803, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_tail16 :
    instructionSequenceAt 51 false { bytes := artifactBytes, pos := 4789, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false).drop 16, .end), { bytes := artifactBytes, pos := 4803, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_tail8 :
    instructionSequenceAt 59 false { bytes := artifactBytes, pos := 4777, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false).drop 8, .end), { bytes := artifactBytes, pos := 4803, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_0_t_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 4755, limit := 4820 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false)[0]!) false).drop 0, .end), { bytes := artifactBytes, pos := 4803, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_tail1 :
    instructionSequenceAt 68 false { bytes := artifactBytes, pos := 4803, limit := 4820 } =
      .ok (((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false).drop 1, .end), { bytes := artifactBytes, pos := 4804, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_2_t_tail0 :
    instructionSequenceAt 69 false { bytes := artifactBytes, pos := 4753, limit := 4820 } =
      .ok (((Instr.childBody ((Cache.raw.codes[36]!.body)[2]!) false).drop 0, .end), { bytes := artifactBytes, pos := 4804, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_6_t_tail2 :
    instructionSequenceAt 63 true { bytes := artifactBytes, pos := 4815, limit := 4820 } =
      .ok (((Instr.childBody ((Cache.raw.codes[36]!.body)[6]!) false).drop 2, .otherwise), { bytes := artifactBytes, pos := 4816, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_6_t_tail0 :
    instructionSequenceAt 65 true { bytes := artifactBytes, pos := 4811, limit := 4820 } =
      .ok (((Instr.childBody ((Cache.raw.codes[36]!.body)[6]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4816, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_6_e_tail0 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 4816, limit := 4820 } =
      .ok (((Instr.childBody ((Cache.raw.codes[36]!.body)[6]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4817, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_tail8 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 4819, limit := 4820 } =
      .ok (((Cache.raw.codes[36]!.body).drop 8, .end), { bytes := artifactBytes, pos := 4820, limit := 4820 }) := by cbv

@[cbv_eval] theorem sequence36_tail0 :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 4747, limit := 4820 } =
      .ok (((Cache.raw.codes[36]!.body).drop 0, .end), { bytes := artifactBytes, pos := 4820, limit := 4820 }) := by cbv

theorem code36_decoded_parts :
    code { bytes := artifactBytes, pos := 4743, limit := 16006 } = .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4820, limit := 16006 }) := by
  refine code_eq_of_parts (size := 76)
    (payload := { bytes := artifactBytes, pos := 4744, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 4747, limit := 4820 })
    (bodyFinish := { bytes := artifactBytes, pos := 4820, limit := 4820 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence36_tail0
  · rfl

#print axioms code36_decoded_parts
end Project.TinyGpt2Hidden.Artifact
