import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code22_seq_22_21_t_69_t_37_t_tail12_decoded :
    instructionSequenceAt 691 true { bytes := artifactBytes, pos := 3289, limit := 3717 } =
      .ok ((((((((((Cache.raw.codes[22]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 12, .otherwise), { bytes := artifactBytes, pos := 3545, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_21_t_69_t_37_t_tail0_decoded :
    instructionSequenceAt 703 true { bytes := artifactBytes, pos := 3270, limit := 3717 } =
      .ok ((((((((((Cache.raw.codes[22]!).body)[21]!).childBody false)[69]!).childBody false)[37]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3545, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_21_t_69_t_tail37_decoded :
    instructionSequenceAt 705 true { bytes := artifactBytes, pos := 3268, limit := 3717 } =
      .ok ((((((((Cache.raw.codes[22]!).body)[21]!).childBody false)[69]!).childBody false).drop 37, .otherwise), { bytes := artifactBytes, pos := 3597, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_21_t_69_t_tail0_decoded :
    instructionSequenceAt 742 true { bytes := artifactBytes, pos := 3151, limit := 3717 } =
      .ok ((((((((Cache.raw.codes[22]!).body)[21]!).childBody false)[69]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3597, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_21_t_tail69_decoded :
    instructionSequenceAt 744 true { bytes := artifactBytes, pos := 3149, limit := 3717 } =
      .ok ((((((Cache.raw.codes[22]!).body)[21]!).childBody false).drop 69, .otherwise), { bytes := artifactBytes, pos := 3649, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_21_t_tail0_decoded :
    instructionSequenceAt 813 true { bytes := artifactBytes, pos := 2928, limit := 3717 } =
      .ok ((((((Cache.raw.codes[22]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3649, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_tail21_decoded :
    instructionSequenceAt 815 false { bytes := artifactBytes, pos := 2926, limit := 3717 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 21, .end), { bytes := artifactBytes, pos := 3717, limit := 3717 }) := by
  cbv

@[cbv_eval] theorem code22_seq_22_tail0_decoded :
    instructionSequenceAt 836 false { bytes := artifactBytes, pos := 2881, limit := 3717 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3717, limit := 3717 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2876, limit := 21767 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 3717, limit := 21767 }) := by
  refine code_eq_of_parts (size := 839)
    (payload := { bytes := artifactBytes, pos := 2878, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 2881, limit := 3717 })
    (bodyFinish := { bytes := artifactBytes, pos := 3717, limit := 3717 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code22_seq_22_tail0_decoded
  · rfl

#print axioms code22_decoded

end Project.EulerRiemann.Artifact
