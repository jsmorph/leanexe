import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_65_tail43 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 28155, limit := 28315 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 43, .end), { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  cbv

@[cbv_eval] theorem sequence_65_tail25 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 28026, limit := 28315 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 25, .end), { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  cbv

@[cbv_eval] theorem sequence_65_tail0 :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 27967, limit := 28315 } =
      .ok ((((Cache.raw.codes[65]!).body).drop 0, .end), { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  cbv

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 27962, limit := 28315 } = .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 28315, limit := 28315 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 27964, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 27967, limit := 28315 })
    (bodyFinish := { bytes := artifactBytes, pos := 28315, limit := 28315 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_65_tail0
  · rfl

#print axioms code65_decoded

end Project.Gpt2QuantizedCached.Artifact
