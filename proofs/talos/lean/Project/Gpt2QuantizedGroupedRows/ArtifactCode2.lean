import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_tail0 :
    instructionSequenceAt 99 false { bytes := artifactBytes, pos := 746, limit := 845 } =
      .ok ((((Cache.raw.codes[2]!).body).drop 0, .end), { bytes := artifactBytes, pos := 845, limit := 845 }) := by
  cbv

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 742, limit := 5409 } = .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 845, limit := 5409 }) := by
  refine code_eq_of_parts (size := 102)
    (payload := { bytes := artifactBytes, pos := 743, limit := 5409 })
    (bodyStart := { bytes := artifactBytes, pos := 746, limit := 845 })
    (bodyFinish := { bytes := artifactBytes, pos := 845, limit := 845 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_2_tail0
  · rfl

#print axioms code2_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
