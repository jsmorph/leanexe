import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_37_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 26608, limit := 26634 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26634, limit := 26634 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 26606, limit := 27068 } = .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 26634, limit := 27068 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 26607, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 26608, limit := 26634 })
    (bodyFinish := { bytes := artifactBytes, pos := 26634, limit := 26634 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_37_tail0
  · rfl

#print axioms code37_decoded

end Project.Beck.Artifact
