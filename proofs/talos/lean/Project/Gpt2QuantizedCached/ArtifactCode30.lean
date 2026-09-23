import Project.Gpt2QuantizedCached.ArtifactCode30Sequences1
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 5650, limit := 28315 } = .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 6531, limit := 28315 }) := by
  refine code_eq_of_parts (size := 879)
    (payload := { bytes := artifactBytes, pos := 5652, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 5655, limit := 6531 })
    (bodyFinish := { bytes := artifactBytes, pos := 6531, limit := 6531 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_30_tail0
  · rfl

#print axioms code30_decoded

end Project.Gpt2QuantizedCached.Artifact
