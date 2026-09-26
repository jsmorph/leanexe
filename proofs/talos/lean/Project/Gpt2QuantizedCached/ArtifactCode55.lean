import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_55_tail0 :
    instructionSequenceAt 7 false { bytes := artifactBytes, pos := 23621, limit := 23628 } =
      .ok ((((Cache.raw.codes[55]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23628, limit := 23628 }) := by
  cbv

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 23617, limit := 28017 } = .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 23628, limit := 28017 }) := by
  refine code_eq_of_parts (size := 10)
    (payload := { bytes := artifactBytes, pos := 23618, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 23621, limit := 23628 })
    (bodyFinish := { bytes := artifactBytes, pos := 23628, limit := 23628 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_55_tail0
  · rfl

#print axioms code55_decoded

end Project.Gpt2QuantizedCached.Artifact
