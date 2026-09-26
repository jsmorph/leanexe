import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 557, limit := 590 } =
      .ok (((Cache.raw.codes[2]!).body, .end), { bytes := artifactBytes, pos := 590, limit := 590 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 553, limit := 4936 } = .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 590, limit := 4936 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 554, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 557, limit := 590 })
    (bodyFinish := { bytes := artifactBytes, pos := 590, limit := 590 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.EulerOutwardSpeed.Artifact
