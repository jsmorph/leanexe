import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_16_tail0 :
    instructionSequenceAt 43 false { bytes := artifactBytes, pos := 1301, limit := 1344 } =
      .ok ((((Cache.raw.codes[16]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1344, limit := 1344 }) := by
  cbv

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 1297, limit := 19083 } = .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 1344, limit := 19083 }) := by
  refine code_eq_of_parts (size := 46)
    (payload := { bytes := artifactBytes, pos := 1298, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1301, limit := 1344 })
    (bodyFinish := { bytes := artifactBytes, pos := 1344, limit := 1344 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_16_tail0
  · rfl

#print axioms code16_decoded

end Project.Gpt2CachedStep.Artifact
