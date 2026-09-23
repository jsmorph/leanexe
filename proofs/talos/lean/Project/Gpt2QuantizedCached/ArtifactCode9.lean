import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 1322, limit := 1389 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1389, limit := 1389 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 1318, limit := 28315 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 1389, limit := 28315 }) := by
  refine code_eq_of_parts (size := 70)
    (payload := { bytes := artifactBytes, pos := 1319, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 1322, limit := 1389 })
    (bodyFinish := { bytes := artifactBytes, pos := 1389, limit := 1389 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.Gpt2QuantizedCached.Artifact
