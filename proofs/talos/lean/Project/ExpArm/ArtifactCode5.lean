import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 10236, limit := 10313 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10313, limit := 10313 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 10232, limit := 10666 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 10313, limit := 10666 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 10233, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 10236, limit := 10313 })
    (bodyFinish := { bytes := artifactBytes, pos := 10313, limit := 10313 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.ExpArm.Artifact
