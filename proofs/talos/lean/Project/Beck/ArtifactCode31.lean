import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_31_tail0 :
    instructionSequenceAt 46 false { bytes := artifactBytes, pos := 18737, limit := 18783 } =
      .ok ((((Cache.raw.codes[31]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18783, limit := 18783 }) := by
  cbv

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 18733, limit := 27068 } = .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 18783, limit := 27068 }) := by
  refine code_eq_of_parts (size := 49)
    (payload := { bytes := artifactBytes, pos := 18734, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 18737, limit := 18783 })
    (bodyFinish := { bytes := artifactBytes, pos := 18783, limit := 18783 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_31_tail0
  · rfl

#print axioms code31_decoded

end Project.Beck.Artifact
