import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_28_tail0 :
    instructionSequenceAt 108 false { bytes := artifactBytes, pos := 2664, limit := 2772 } =
      .ok ((((Cache.raw.codes[28]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2772, limit := 2772 }) := by
  cbv

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 2660, limit := 5720 } = .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 2772, limit := 5720 }) := by
  refine code_eq_of_parts (size := 111)
    (payload := { bytes := artifactBytes, pos := 2661, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 2664, limit := 2772 })
    (bodyFinish := { bytes := artifactBytes, pos := 2772, limit := 2772 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_28_tail0
  · rfl

#print axioms code28_decoded

end Project.EulerOutwardGrid.Artifact
