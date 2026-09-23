import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 2301, limit := 2334 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2334, limit := 2334 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 2297, limit := 5441 } = .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 2334, limit := 5441 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 2298, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 2301, limit := 2334 })
    (bodyFinish := { bytes := artifactBytes, pos := 2334, limit := 2334 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
