import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_13_tail0 :
    instructionSequenceAt 95 false { bytes := artifactBytes, pos := 1132, limit := 1227 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1227, limit := 1227 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1128, limit := 5720 } = .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1227, limit := 5720 }) := by
  refine code_eq_of_parts (size := 98)
    (payload := { bytes := artifactBytes, pos := 1129, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 1132, limit := 1227 })
    (bodyFinish := { bytes := artifactBytes, pos := 1227, limit := 1227 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_13_tail0
  · rfl

#print axioms code13_decoded

end Project.EulerOutwardGrid.Artifact
