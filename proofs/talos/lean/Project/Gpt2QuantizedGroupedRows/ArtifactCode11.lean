import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_11_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 4979, limit := 5056 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5056, limit := 5056 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 4975, limit := 5409 } = .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 5056, limit := 5409 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 4976, limit := 5409 })
    (bodyStart := { bytes := artifactBytes, pos := 4979, limit := 5056 })
    (bodyFinish := { bytes := artifactBytes, pos := 5056, limit := 5056 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_11_tail0
  · rfl

#print axioms code11_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
