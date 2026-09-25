import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_40_tail0 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 11111, limit := 11144 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11144, limit := 11144 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 11107, limit := 28017 } = .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 11144, limit := 28017 }) := by
  refine code_eq_of_parts (size := 36)
    (payload := { bytes := artifactBytes, pos := 11108, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 11111, limit := 11144 })
    (bodyFinish := { bytes := artifactBytes, pos := 11144, limit := 11144 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_40_tail0
  · rfl

#print axioms code40_decoded

end Project.Gpt2QuantizedCached.Artifact
