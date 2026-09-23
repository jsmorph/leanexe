import Project.Gpt2QuantizedCached.ArtifactCode37Sequences2
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 9735, limit := 28315 } = .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 10891, limit := 28315 }) := by
  refine code_eq_of_parts (size := 1154)
    (payload := { bytes := artifactBytes, pos := 9737, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 9740, limit := 10891 })
    (bodyFinish := { bytes := artifactBytes, pos := 10891, limit := 10891 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_37_tail0
  · rfl

#print axioms code37_decoded

end Project.Gpt2QuantizedCached.Artifact
