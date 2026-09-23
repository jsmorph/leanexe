import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_12_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 5281, limit := 5441 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 43, .end), { bytes := artifactBytes, pos := 5441, limit := 5441 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 5152, limit := 5441 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 25, .end), { bytes := artifactBytes, pos := 5441, limit := 5441 }) := by
  cbv

@[cbv_eval] theorem sequence_12_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 5093, limit := 5441 } =
      .ok ((((Cache.raw.codes[12]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5441, limit := 5441 }) := by
  cbv

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 5088, limit := 5441 } = .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 5441, limit := 5441 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 5090, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 5093, limit := 5441 })
    (bodyFinish := { bytes := artifactBytes, pos := 5441, limit := 5441 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_12_tail0
  · rfl

#print axioms code12_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
