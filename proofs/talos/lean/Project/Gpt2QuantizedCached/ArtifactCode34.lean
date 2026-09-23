import Project.Gpt2QuantizedCached.ArtifactCode34Sequences4
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 7143, limit := 28315 } = .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 9283, limit := 28315 }) := by
  refine code_eq_of_parts (size := 2138)
    (payload := { bytes := artifactBytes, pos := 7145, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 7148, limit := 9283 })
    (bodyFinish := { bytes := artifactBytes, pos := 9283, limit := 9283 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_34_tail0
  · rfl

#print axioms code34_decoded

end Project.Gpt2QuantizedCached.Artifact
