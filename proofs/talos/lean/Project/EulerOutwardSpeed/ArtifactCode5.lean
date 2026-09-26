import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 764, limit := 783 } =
      .ok (((Cache.raw.codes[5]!).body, .end), { bytes := artifactBytes, pos := 783, limit := 783 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 760, limit := 4936 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 783, limit := 4936 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 761, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 764, limit := 783 })
    (bodyFinish := { bytes := artifactBytes, pos := 783, limit := 783 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.EulerOutwardSpeed.Artifact
