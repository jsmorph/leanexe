import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode50Sequences7

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 15663, limit := 28017 } = .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 19374, limit := 28017 }) := by
  refine code_eq_of_parts (size := 3709)
    (payload := { bytes := artifactBytes, pos := 15665, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 15668, limit := 19374 })
    (bodyFinish := { bytes := artifactBytes, pos := 19374, limit := 19374 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_50_tail0
  · rfl

#print axioms code50_decoded

end Project.Gpt2QuantizedCached.Artifact
