import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 38 false { bytes := artifactBytes, pos := 722, limit := 760 } =
      .ok (((Cache.raw.codes[4]!).body, .end), { bytes := artifactBytes, pos := 760, limit := 760 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 718, limit := 4936 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 760, limit := 4936 }) := by
  refine code_eq_of_parts (size := 41)
    (payload := { bytes := artifactBytes, pos := 719, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 722, limit := 760 })
    (bodyFinish := { bytes := artifactBytes, pos := 760, limit := 760 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.EulerOutwardSpeed.Artifact
