import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_10_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 4981, limit := 5007 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5007, limit := 5007 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 4979, limit := 5441 } = .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 5007, limit := 5441 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 4980, limit := 5441 })
    (bodyStart := { bytes := artifactBytes, pos := 4981, limit := 5007 })
    (bodyFinish := { bytes := artifactBytes, pos := 5007, limit := 5007 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_10_tail0
  · rfl

#print axioms code10_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
