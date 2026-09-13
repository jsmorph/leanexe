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

@[cbv_eval] theorem code97_seq_97_4_e_tail28_decoded :
    instructionSequenceAt 483 false { bytes := artifactBytes, pos := 17671, limit := 18023 } =
      .ok ((((((Cache.raw.codes[97]!).body)[4]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 18014, limit := 18023 }) := by
  cbv

@[cbv_eval] theorem code97_seq_97_4_e_tail0_decoded :
    instructionSequenceAt 511 false { bytes := artifactBytes, pos := 17617, limit := 18023 } =
      .ok ((((((Cache.raw.codes[97]!).body)[4]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 18014, limit := 18023 }) := by
  cbv

@[cbv_eval] theorem code97_seq_97_tail4_decoded :
    instructionSequenceAt 513 false { bytes := artifactBytes, pos := 17523, limit := 18023 } =
      .ok ((((Cache.raw.codes[97]!).body).drop 4, .end), { bytes := artifactBytes, pos := 18023, limit := 18023 }) := by
  cbv

@[cbv_eval] theorem code97_seq_97_tail0_decoded :
    instructionSequenceAt 517 false { bytes := artifactBytes, pos := 17506, limit := 18023 } =
      .ok ((((Cache.raw.codes[97]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18023, limit := 18023 }) := by
  cbv

theorem code97_decoded :
    code { bytes := artifactBytes, pos := 17501, limit := 21767 } =
      .ok (Cache.raw.codes[97]!, { bytes := artifactBytes, pos := 18023, limit := 21767 }) := by
  refine code_eq_of_parts (size := 520)
    (payload := { bytes := artifactBytes, pos := 17503, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 17506, limit := 18023 })
    (bodyFinish := { bytes := artifactBytes, pos := 18023, limit := 18023 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code97_seq_97_tail0_decoded
  · rfl

#print axioms code97_decoded

end Project.EulerRiemann.Artifact
