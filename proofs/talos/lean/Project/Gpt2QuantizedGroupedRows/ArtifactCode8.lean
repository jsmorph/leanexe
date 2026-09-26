import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode8Sequences3

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 2341, limit := 5409 } = .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 4580, limit := 5409 }) := by
  refine code_eq_of_parts (size := 2237)
    (payload := { bytes := artifactBytes, pos := 2343, limit := 5409 })
    (bodyStart := { bytes := artifactBytes, pos := 2346, limit := 4580 })
    (bodyFinish := { bytes := artifactBytes, pos := 4580, limit := 4580 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_8_tail0
  · rfl

#print axioms code8_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
