import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence43_3_t_tail6 :
    instructionSequenceAt 13 true { bytes := artifactBytes, pos := 5468, limit := 5477 } =
      .ok (((Instr.childBody ((Cache.raw.codes[43]!.body)[3]!) false).drop 6, .otherwise), { bytes := artifactBytes, pos := 5469, limit := 5477 }) := by cbv

@[cbv_eval] theorem sequence43_3_t_tail0 :
    instructionSequenceAt 19 true { bytes := artifactBytes, pos := 5460, limit := 5477 } =
      .ok (((Instr.childBody ((Cache.raw.codes[43]!.body)[3]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 5469, limit := 5477 }) := by cbv

@[cbv_eval] theorem sequence43_3_e_tail1 :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 5471, limit := 5477 } =
      .ok (((Instr.childBody ((Cache.raw.codes[43]!.body)[3]!) true).drop 1, .end), { bytes := artifactBytes, pos := 5472, limit := 5477 }) := by cbv

@[cbv_eval] theorem sequence43_3_e_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 5469, limit := 5477 } =
      .ok (((Instr.childBody ((Cache.raw.codes[43]!.body)[3]!) true).drop 0, .end), { bytes := artifactBytes, pos := 5472, limit := 5477 }) := by cbv

@[cbv_eval] theorem sequence43_tail6 :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 5476, limit := 5477 } =
      .ok (((Cache.raw.codes[43]!.body).drop 6, .end), { bytes := artifactBytes, pos := 5477, limit := 5477 }) := by cbv

@[cbv_eval] theorem sequence43_tail0 :
    instructionSequenceAt 24 false { bytes := artifactBytes, pos := 5453, limit := 5477 } =
      .ok (((Cache.raw.codes[43]!.body).drop 0, .end), { bytes := artifactBytes, pos := 5477, limit := 5477 }) := by cbv

theorem code43_decoded_parts :
    code { bytes := artifactBytes, pos := 5449, limit := 16006 } = .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5477, limit := 16006 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 5450, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 5453, limit := 5477 })
    (bodyFinish := { bytes := artifactBytes, pos := 5477, limit := 5477 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence43_tail0
  · rfl

#print axioms code43_decoded_parts
end Project.TinyGpt2Hidden.Artifact
