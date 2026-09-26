import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_7_tail0 :
    instructionSequenceAt 18 false { bytes := artifactBytes, pos := 824, limit := 842 } =
      .ok (((Cache.raw.codes[7]!).body, .end), { bytes := artifactBytes, pos := 842, limit := 842 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 820, limit := 4936 } = .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 842, limit := 4936 }) := by
  refine code_eq_of_parts (size := 21)
    (payload := { bytes := artifactBytes, pos := 821, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 824, limit := 842 })
    (bodyFinish := { bytes := artifactBytes, pos := 842, limit := 842 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_7_tail0
  · rfl

#print axioms code7_decoded

end Project.EulerOutwardSpeed.Artifact
