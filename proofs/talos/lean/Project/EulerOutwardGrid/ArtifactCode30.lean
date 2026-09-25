import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_47_t_tail26 :
    instructionSequenceAt 271 true { bytes := artifactBytes, pos := 3078, limit := 3235 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 3215, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem sequence_30_47_t_tail0 :
    instructionSequenceAt 297 true { bytes := artifactBytes, pos := 3018, limit := 3235 } =
      .ok ((((((Cache.raw.codes[30]!).body)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3215, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail47 :
    instructionSequenceAt 299 false { bytes := artifactBytes, pos := 3016, limit := 3235 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 47, .end), { bytes := artifactBytes, pos := 3235, limit := 3235 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail0 :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 2889, limit := 3235 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 3235, limit := 3235 }) := by
  cbv

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 2884, limit := 5720 } = .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 3235, limit := 5720 }) := by
  refine code_eq_of_parts (size := 349)
    (payload := { bytes := artifactBytes, pos := 2886, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2889, limit := 3235 })
    (bodyFinish := { bytes := artifactBytes, pos := 3235, limit := 3235 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_30_tail0
  · rfl

#print axioms code30_decoded

end Project.EulerOutwardGrid.Artifact
