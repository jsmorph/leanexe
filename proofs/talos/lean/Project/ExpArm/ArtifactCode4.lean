import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 10206, limit := 10232 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10232, limit := 10232 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 10204, limit := 10666 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 10232, limit := 10666 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 10205, limit := 10666 })
    (bodyStart := { bytes := artifactBytes, pos := 10206, limit := 10232 })
    (bodyFinish := { bytes := artifactBytes, pos := 10232, limit := 10232 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.ExpArm.Artifact
