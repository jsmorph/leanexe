import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 2278, limit := 2297 } =
      .ok ((((Cache.raw.codes[5]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2297, limit := 2297 }) := by
  cbv

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 2274, limit := 5441 } = .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 2297, limit := 5441 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 2275, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 2278, limit := 2297 })
    (bodyFinish := { bytes := artifactBytes, pos := 2297, limit := 2297 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_5_tail0
  · rfl

#print axioms code5_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
