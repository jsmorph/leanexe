import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedCached.ArtifactCode59Sequences2

namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code59_decoded :
    code { bytes := artifactBytes, pos := 25750, limit := 28017 } = .ok (Cache.raw.codes[59]!, { bytes := artifactBytes, pos := 27117, limit := 28017 }) := by
  refine code_eq_of_parts (size := 1365)
    (payload := { bytes := artifactBytes, pos := 25752, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 25755, limit := 27117 })
    (bodyFinish := { bytes := artifactBytes, pos := 27117, limit := 27117 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_59_tail0
  · rfl

#print axioms code59_decoded

end Project.Gpt2QuantizedCached.Artifact
