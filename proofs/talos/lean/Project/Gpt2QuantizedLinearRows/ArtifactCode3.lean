import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode3Sequences2

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 838, limit := 4741 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 1994, limit := 4741 }) := by
  refine code_eq_of_parts (size := 1154)
    (payload := { bytes := artifactBytes, pos := 840, limit := 4741 })
    (bodyStart := { bytes := artifactBytes, pos := 843, limit := 1994 })
    (bodyFinish := { bytes := artifactBytes, pos := 1994, limit := 1994 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
