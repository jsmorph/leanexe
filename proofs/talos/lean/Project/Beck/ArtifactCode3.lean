import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_3_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 2029, limit := 2036 } =
      .ok ((((Cache.raw.codes[3]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2036, limit := 2036 }) := by
  cbv

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 2025, limit := 27068 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 2036, limit := 27068 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 2026, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 2029, limit := 2036 })
    (bodyFinish := { bytes := artifactBytes, pos := 2036, limit := 2036 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Beck.Artifact
