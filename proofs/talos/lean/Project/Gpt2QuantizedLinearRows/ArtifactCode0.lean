import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 85 false { bytes := artifactBytes, pos := 309, limit := 394 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 394, limit := 394 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 305, limit := 4757 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 394, limit := 4757 }) := by
  refine code_eq_of_parts (size := 88)
    (payload := { bytes := artifactBytes, pos := 306, limit := 4757 })
    (bodyStart := { bytes := artifactBytes, pos := 309, limit := 394 })
    (bodyFinish := { bytes := artifactBytes, pos := 394, limit := 394 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
