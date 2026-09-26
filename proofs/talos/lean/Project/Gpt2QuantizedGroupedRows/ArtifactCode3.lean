import Project.Gpt2QuantizedGroupedRows.ArtifactByteLookup
import Project.Gpt2QuantizedGroupedRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedGroupedRows.ArtifactCode3Sequences2

namespace Project.Gpt2QuantizedGroupedRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 845, limit := 5409 } = .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 2001, limit := 5409 }) := by
  refine code_eq_of_parts (size := 1154)
    (payload := { bytes := artifactBytes, pos := 847, limit := 5409 })
    (bodyStart := { bytes := artifactBytes, pos := 850, limit := 2001 })
    (bodyFinish := { bytes := artifactBytes, pos := 2001, limit := 2001 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_3_tail0
  · rfl

#print axioms code3_decoded

end Project.Gpt2QuantizedGroupedRows.Artifact
