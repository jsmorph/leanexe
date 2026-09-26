import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_20_tail0 :
    instructionSequenceAt 65 false { bytes := artifactBytes, pos := 2095, limit := 2160 } =
      .ok ((((Cache.raw.codes[20]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2160, limit := 2160 }) := by
  cbv

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2091, limit := 28017 } = .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2160, limit := 28017 }) := by
  refine code_eq_of_parts (size := 68)
    (payload := { bytes := artifactBytes, pos := 2092, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 2095, limit := 2160 })
    (bodyFinish := { bytes := artifactBytes, pos := 2160, limit := 2160 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_20_tail0
  · rfl

#print axioms code20_decoded

end Project.Gpt2QuantizedCached.Artifact
