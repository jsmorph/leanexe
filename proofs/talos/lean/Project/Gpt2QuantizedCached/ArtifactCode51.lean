import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode51Sequences1

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 19374, limit := 28017 } = .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 19931, limit := 28017 }) := by
  refine code_eq_of_parts (size := 555)
    (payload := { bytes := artifactBytes, pos := 19376, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 19379, limit := 19931 })
    (bodyFinish := { bytes := artifactBytes, pos := 19931, limit := 19931 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_51_tail0
  · rfl

#print axioms code51_decoded

end Project.Gpt2QuantizedCached.Artifact
