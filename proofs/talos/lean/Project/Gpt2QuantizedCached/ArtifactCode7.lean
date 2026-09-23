import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_7_tail0 :
    instructionSequenceAt 66 false { bytes := artifactBytes, pos := 1182, limit := 1248 } =
      .ok ((((Cache.raw.codes[7]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1248, limit := 1248 }) := by
  cbv

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 1178, limit := 28315 } = .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 1248, limit := 28315 }) := by
  refine code_eq_of_parts (size := 69)
    (payload := { bytes := artifactBytes, pos := 1179, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 1182, limit := 1248 })
    (bodyFinish := { bytes := artifactBytes, pos := 1248, limit := 1248 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_7_tail0
  · rfl

#print axioms code7_decoded

end Project.Gpt2QuantizedCached.Artifact
