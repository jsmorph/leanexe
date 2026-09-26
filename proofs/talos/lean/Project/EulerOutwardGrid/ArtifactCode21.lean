import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_21_17_t_tail28 :
    instructionSequenceAt 279 true { bytes := artifactBytes, pos := 1989, limit := 2126 } =
      .ok ((((((Cache.raw.codes[21]!).body)[17]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 2118, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem sequence_21_17_t_tail0 :
    instructionSequenceAt 307 true { bytes := artifactBytes, pos := 1891, limit := 2126 } =
      .ok ((((((Cache.raw.codes[21]!).body)[17]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2118, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem sequence_21_tail17 :
    instructionSequenceAt 309 false { bytes := artifactBytes, pos := 1889, limit := 2126 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 17, .end), { bytes := artifactBytes, pos := 2126, limit := 2126 }) := by
  cbv

@[cbv_eval] theorem sequence_21_tail0 :
    instructionSequenceAt 326 false { bytes := artifactBytes, pos := 1800, limit := 2126 } =
      .ok ((((Cache.raw.codes[21]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2126, limit := 2126 }) := by
  cbv

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 1795, limit := 5720 } = .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2126, limit := 5720 }) := by
  refine code_eq_of_parts (size := 329)
    (payload := { bytes := artifactBytes, pos := 1797, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1800, limit := 2126 })
    (bodyFinish := { bytes := artifactBytes, pos := 2126, limit := 2126 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_21_tail0
  · rfl

#print axioms code21_decoded

end Project.EulerOutwardGrid.Artifact
