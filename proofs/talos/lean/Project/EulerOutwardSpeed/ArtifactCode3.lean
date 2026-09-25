import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 124 false { bytes := artifactBytes, pos := 594, limit := 718 } =
      .ok (((Cache.raw.codes[3]!).body, .end), { bytes := artifactBytes, pos := 718, limit := 718 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 590, limit := 4936 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 718, limit := 4936 }) := by
  refine code_eq_of_parts (size := 127)
    (payload := { bytes := artifactBytes, pos := 591, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 594, limit := 718 })
    (bodyFinish := { bytes := artifactBytes, pos := 718, limit := 718 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.EulerOutwardSpeed.Artifact
