import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 67 false { bytes := artifactBytes, pos := 809, limit := 876 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 876, limit := 876 }) := by
  cbv

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 805, limit := 19083 } = .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 876, limit := 19083 }) := by
  refine code_eq_of_parts (size := 70)
    (payload := { bytes := artifactBytes, pos := 806, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 809, limit := 876 })
    (bodyFinish := { bytes := artifactBytes, pos := 876, limit := 876 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_6_tail0
  · rfl

#print axioms code6_decoded

end Project.Gpt2CachedStep.Artifact
