import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_0_tail0 :
    instructionSequenceAt 9 false { bytes := artifactBytes, pos := 557, limit := 566 } =
      .ok ((((Cache.raw.codes[0]!).body).drop 0, .end), { bytes := artifactBytes, pos := 566, limit := 566 }) := by
  cbv

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 553, limit := 19083 } = .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 566, limit := 19083 }) := by
  refine code_eq_of_parts (size := 12)
    (payload := { bytes := artifactBytes, pos := 554, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 557, limit := 566 })
    (bodyFinish := { bytes := artifactBytes, pos := 566, limit := 566 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_0_tail0
  · rfl

#print axioms code0_decoded

end Project.Gpt2CachedStep.Artifact
