import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_11_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 4311, limit := 4388 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4388, limit := 4388 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 4307, limit := 4741 } = .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 4388, limit := 4741 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 4308, limit := 4741 })
    (bodyStart := { bytes := artifactBytes, pos := 4311, limit := 4388 })
    (bodyFinish := { bytes := artifactBytes, pos := 4388, limit := 4388 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_11_tail0
  · rfl

#print axioms code11_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
