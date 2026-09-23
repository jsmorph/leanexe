import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_17_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 1884, limit := 1951 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1951, limit := 1951 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 1880, limit := 28315 } = .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 1951, limit := 28315 }) := by
  refine code_eq_of_parts (size := 70)
    (payload := { bytes := artifactBytes, pos := 1881, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 1884, limit := 1951 })
    (bodyFinish := { bytes := artifactBytes, pos := 1951, limit := 1951 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_17_tail0
  · rfl

#print axioms code17_decoded

end Project.Gpt2QuantizedCached.Artifact
