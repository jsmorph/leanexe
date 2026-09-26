import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_10_tail0 :
    instructionSequenceAt 66 false { bytes := artifactBytes, pos := 1393, limit := 1459 } =
      .ok ((((Cache.raw.codes[10]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1459, limit := 1459 }) := by
  cbv

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 1389, limit := 28017 } = .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 1459, limit := 28017 }) := by
  refine code_eq_of_parts (size := 69)
    (payload := { bytes := artifactBytes, pos := 1390, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 1393, limit := 1459 })
    (bodyFinish := { bytes := artifactBytes, pos := 1459, limit := 1459 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_10_tail0
  · rfl

#print axioms code10_decoded

end Project.Gpt2QuantizedCached.Artifact
