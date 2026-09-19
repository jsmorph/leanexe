import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_9_tail0 :
    instructionSequenceAt 31 false { bytes := artifactBytes, pos := 950, limit := 981 } =
      .ok ((((Cache.raw.codes[9]!).body).drop 0, .end), { bytes := artifactBytes, pos := 981, limit := 981 }) := by
  cbv

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 946, limit := 19083 } = .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 981, limit := 19083 }) := by
  refine code_eq_of_parts (size := 34)
    (payload := { bytes := artifactBytes, pos := 947, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 950, limit := 981 })
    (bodyFinish := { bytes := artifactBytes, pos := 981, limit := 981 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_9_tail0
  · rfl

#print axioms code9_decoded

end Project.Gpt2CachedStep.Artifact
