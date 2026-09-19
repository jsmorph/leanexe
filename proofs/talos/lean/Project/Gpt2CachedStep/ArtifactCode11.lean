import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_11_tail0 :
    instructionSequenceAt 31 false { bytes := artifactBytes, pos := 1056, limit := 1087 } =
      .ok ((((Cache.raw.codes[11]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1087, limit := 1087 }) := by
  cbv

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 1052, limit := 19083 } = .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 1087, limit := 19083 }) := by
  refine code_eq_of_parts (size := 34)
    (payload := { bytes := artifactBytes, pos := 1053, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1056, limit := 1087 })
    (bodyFinish := { bytes := artifactBytes, pos := 1087, limit := 1087 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_11_tail0
  · rfl

#print axioms code11_decoded

end Project.Gpt2CachedStep.Artifact
