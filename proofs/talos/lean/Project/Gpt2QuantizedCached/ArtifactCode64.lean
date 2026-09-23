import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_64_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 27885, limit := 27962 } =
      .ok ((((Cache.raw.codes[64]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27962, limit := 27962 }) := by
  cbv

theorem code64_decoded :
    code { bytes := artifactBytes, pos := 27881, limit := 28315 } = .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 27962, limit := 28315 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 27882, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 27885, limit := 27962 })
    (bodyFinish := { bytes := artifactBytes, pos := 27962, limit := 27962 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_64_tail0
  · rfl

#print axioms code64_decoded

end Project.Gpt2QuantizedCached.Artifact
