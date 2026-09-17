import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence32_3_t_3_t_3_t_tail1 :
    instructionSequenceAt 73 true { bytes := artifactBytes, pos := 4368, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) false)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 4369, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_t_3_t_tail0 :
    instructionSequenceAt 74 true { bytes := artifactBytes, pos := 4366, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) false)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4369, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_t_3_e_tail1 :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 4371, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) false)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 4372, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_t_3_e_tail0 :
    instructionSequenceAt 74 false { bytes := artifactBytes, pos := 4369, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) false)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4372, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_e_3_t_tail1 :
    instructionSequenceAt 73 true { bytes := artifactBytes, pos := 4405, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) true)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 4406, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_e_3_t_tail0 :
    instructionSequenceAt 74 true { bytes := artifactBytes, pos := 4403, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) true)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4406, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_e_3_e_tail1 :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 4408, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) true)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 4409, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_e_3_e_tail0 :
    instructionSequenceAt 74 false { bytes := artifactBytes, pos := 4406, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) true)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4409, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_t_tail4 :
    instructionSequenceAt 75 true { bytes := artifactBytes, pos := 4372, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) false).drop 4, .otherwise), { bytes := artifactBytes, pos := 4373, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_t_tail0 :
    instructionSequenceAt 79 true { bytes := artifactBytes, pos := 4359, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4373, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_e_tail1 :
    instructionSequenceAt 78 false { bytes := artifactBytes, pos := 4375, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 4376, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_3_e_tail0 :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 4373, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4376, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_t_tail1 :
    instructionSequenceAt 78 true { bytes := artifactBytes, pos := 4395, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 4396, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_t_tail0 :
    instructionSequenceAt 79 true { bytes := artifactBytes, pos := 4393, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4396, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_e_tail4 :
    instructionSequenceAt 75 false { bytes := artifactBytes, pos := 4409, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) true).drop 4, .end), { bytes := artifactBytes, pos := 4410, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_3_e_tail0 :
    instructionSequenceAt 79 false { bytes := artifactBytes, pos := 4396, limit := 4416 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4410, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_tail4 :
    instructionSequenceAt 80 true { bytes := artifactBytes, pos := 4376, limit := 4416 } =
      .ok (((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false).drop 4, .otherwise), { bytes := artifactBytes, pos := 4377, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_t_tail0 :
    instructionSequenceAt 84 true { bytes := artifactBytes, pos := 4343, limit := 4416 } =
      .ok (((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4377, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_tail4 :
    instructionSequenceAt 80 false { bytes := artifactBytes, pos := 4410, limit := 4416 } =
      .ok (((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true).drop 4, .end), { bytes := artifactBytes, pos := 4411, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_3_e_tail0 :
    instructionSequenceAt 84 false { bytes := artifactBytes, pos := 4377, limit := 4416 } =
      .ok (((Instr.childBody ((Cache.raw.codes[32]!.body)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 4411, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_tail6 :
    instructionSequenceAt 83 false { bytes := artifactBytes, pos := 4415, limit := 4416 } =
      .ok (((Cache.raw.codes[32]!.body).drop 6, .end), { bytes := artifactBytes, pos := 4416, limit := 4416 }) := by cbv

@[cbv_eval] theorem sequence32_tail0 :
    instructionSequenceAt 89 false { bytes := artifactBytes, pos := 4327, limit := 4416 } =
      .ok (((Cache.raw.codes[32]!.body).drop 0, .end), { bytes := artifactBytes, pos := 4416, limit := 4416 }) := by cbv

theorem code32_decoded_parts :
    code { bytes := artifactBytes, pos := 4323, limit := 16006 } = .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 4416, limit := 16006 }) := by
  refine code_eq_of_parts (size := 92)
    (payload := { bytes := artifactBytes, pos := 4324, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 4327, limit := 4416 })
    (bodyFinish := { bytes := artifactBytes, pos := 4416, limit := 4416 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence32_tail0
  · rfl

#print axioms code32_decoded_parts
end Project.TinyGpt2Hidden.Artifact
