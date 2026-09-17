import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence41_3_t_tail12 :
    instructionSequenceAt 19 true { bytes := artifactBytes, pos := 5411, limit := 5420 } =
      .ok (((Instr.childBody ((Cache.raw.codes[41]!.body)[3]!) false).drop 12, .otherwise), { bytes := artifactBytes, pos := 5412, limit := 5420 }) := by cbv

@[cbv_eval] theorem sequence41_3_t_tail8 :
    instructionSequenceAt 23 true { bytes := artifactBytes, pos := 5403, limit := 5420 } =
      .ok (((Instr.childBody ((Cache.raw.codes[41]!.body)[3]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 5412, limit := 5420 }) := by cbv

@[cbv_eval] theorem sequence41_3_t_tail0 :
    instructionSequenceAt 31 true { bytes := artifactBytes, pos := 5391, limit := 5420 } =
      .ok (((Instr.childBody ((Cache.raw.codes[41]!.body)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5412, limit := 5420 }) := by cbv

@[cbv_eval] theorem sequence41_3_e_tail2 :
    instructionSequenceAt 29 false { bytes := artifactBytes, pos := 5416, limit := 5420 } =
      .ok (((Instr.childBody ((Cache.raw.codes[41]!.body)[3]!) true).drop 2, .end), { bytes := artifactBytes, pos := 5417, limit := 5420 }) := by cbv

@[cbv_eval] theorem sequence41_3_e_tail0 :
    instructionSequenceAt 31 false { bytes := artifactBytes, pos := 5412, limit := 5420 } =
      .ok (((Instr.childBody ((Cache.raw.codes[41]!.body)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 5417, limit := 5420 }) := by cbv

@[cbv_eval] theorem sequence41_tail5 :
    instructionSequenceAt 31 false { bytes := artifactBytes, pos := 5419, limit := 5420 } =
      .ok (((Cache.raw.codes[41]!.body).drop 5, .end), { bytes := artifactBytes, pos := 5420, limit := 5420 }) := by cbv

@[cbv_eval] theorem sequence41_tail0 :
    instructionSequenceAt 36 false { bytes := artifactBytes, pos := 5384, limit := 5420 } =
      .ok (((Cache.raw.codes[41]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5420, limit := 5420 }) := by cbv

theorem code41_decoded_parts :
    code { bytes := artifactBytes, pos := 5380, limit := 16006 } = .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5420, limit := 16006 }) := by
  refine code_eq_of_parts (size := 39)
    (payload := { bytes := artifactBytes, pos := 5381, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5384, limit := 5420 })
    (bodyFinish := { bytes := artifactBytes, pos := 5420, limit := 5420 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence41_tail0
  · rfl

#print axioms code41_decoded_parts
end Project.TinyGpt2Hidden.Artifact
