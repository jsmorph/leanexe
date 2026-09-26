import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_56_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 23632, limit := 23651 } =
      .ok ((((Cache.raw.codes[56]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23651, limit := 23651 }) := by
  cbv

theorem code56_decoded :
    code { bytes := artifactBytes, pos := 23628, limit := 28017 } = .ok (Cache.raw.codes[56]!, { bytes := artifactBytes, pos := 23651, limit := 28017 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 23629, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 23632, limit := 23651 })
    (bodyFinish := { bytes := artifactBytes, pos := 23651, limit := 23651 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_56_tail0
  · rfl

#print axioms code56_decoded

end Project.Gpt2QuantizedCached.Artifact
