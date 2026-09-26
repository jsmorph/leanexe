import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode8Sequences2

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 2334, limit := 4741 } = .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 3912, limit := 4741 }) := by
  refine code_eq_of_parts (size := 1576)
    (payload := { bytes := artifactBytes, pos := 2336, limit := 4741 })
    (bodyStart := { bytes := artifactBytes, pos := 2339, limit := 3912 })
    (bodyFinish := { bytes := artifactBytes, pos := 3912, limit := 3912 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
