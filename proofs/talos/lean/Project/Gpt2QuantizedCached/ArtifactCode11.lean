import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_11_tail0 :
    instructionSequenceAt 66 false { bytes := artifactBytes, pos := 1463, limit := 1529 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1529, limit := 1529 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1459, limit := 28017 } = .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1529, limit := 28017 }) := by
  refine code_eq_of_parts (size := 69)
    (payload := { bytes := artifactBytes, pos := 1460, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 1463, limit := 1529 })
    (bodyFinish := { bytes := artifactBytes, pos := 1529, limit := 1529 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_11_tail0
  · rfl

#print axioms code11_decoded

end Project.Gpt2QuantizedCached.Artifact
