import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 85 false { bytes := artifactBytes, pos := 316, limit := 401 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 401, limit := 401 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 312, limit := 5441 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 401, limit := 5441 }) := by
  refine code_eq_of_parts (size := 88)
    (payload := { bytes := artifactBytes, pos := 313, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 316, limit := 401 })
    (bodyFinish := { bytes := artifactBytes, pos := 401, limit := 401 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
