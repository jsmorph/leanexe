import Project.Gpt2QuantizedCached.ArtifactCode59Sequences2
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code59_decoded :
    code { bytes := artifactBytes, pos := 26048, limit := 28315 } = .ok (Cache.raw.codes[59]!, { bytes := artifactBytes, pos := 27415, limit := 28315 }) := by
  refine code_eq_of_parts (size := 1365)
    (payload := { bytes := artifactBytes, pos := 26050, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 26053, limit := 27415 })
    (bodyFinish := { bytes := artifactBytes, pos := 27415, limit := 27415 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_59_tail0
  · rfl

#print axioms code59_decoded

end Project.Gpt2QuantizedCached.Artifact
