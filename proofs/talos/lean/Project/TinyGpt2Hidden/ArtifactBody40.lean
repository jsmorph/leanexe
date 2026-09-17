import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence40_3_t_tail2 :
    instructionSequenceAt 79 true { bytes := artifactBytes, pos := 5313, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) false).drop 2, .otherwise), { bytes := artifactBytes, pos := 5314, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_3_t_tail0 :
    instructionSequenceAt 81 true { bytes := artifactBytes, pos := 5309, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5314, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_3_e_tail31 :
    instructionSequenceAt 50 false { bytes := artifactBytes, pos := 5376, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) true).drop 31, .end), { bytes := artifactBytes, pos := 5377, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_3_e_tail24 :
    instructionSequenceAt 57 false { bytes := artifactBytes, pos := 5362, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) true).drop 24, .end), { bytes := artifactBytes, pos := 5377, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_3_e_tail16 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 5346, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) true).drop 16, .end), { bytes := artifactBytes, pos := 5377, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_3_e_tail8 :
    instructionSequenceAt 73 false { bytes := artifactBytes, pos := 5330, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) true).drop 8, .end), { bytes := artifactBytes, pos := 5377, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_3_e_tail0 :
    instructionSequenceAt 81 false { bytes := artifactBytes, pos := 5314, limit := 5380 } =
      .ok (((Instr.childBody ((Cache.raw.codes[40]!.body)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 5377, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_tail5 :
    instructionSequenceAt 81 false { bytes := artifactBytes, pos := 5379, limit := 5380 } =
      .ok (((Cache.raw.codes[40]!.body).drop 5, .end), { bytes := artifactBytes, pos := 5380, limit := 5380 }) := by cbv

@[cbv_eval] theorem sequence40_tail0 :
    instructionSequenceAt 86 false { bytes := artifactBytes, pos := 5294, limit := 5380 } =
      .ok (((Cache.raw.codes[40]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5380, limit := 5380 }) := by cbv

theorem code40_decoded_parts :
    code { bytes := artifactBytes, pos := 5290, limit := 16006 } = .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 5380, limit := 16006 }) := by
  refine code_eq_of_parts (size := 89)
    (payload := { bytes := artifactBytes, pos := 5291, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5294, limit := 5380 })
    (bodyFinish := { bytes := artifactBytes, pos := 5380, limit := 5380 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence40_tail0
  · rfl

#print axioms code40_decoded_parts
end Project.TinyGpt2Hidden.Artifact
