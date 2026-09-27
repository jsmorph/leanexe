import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_1_tail0 :
    instructionSequenceAt 45 false { bytes := artifactBytes, pos := 570, limit := 615 } =
      .ok ((((Cache.raw.codes[1]!).body).drop 0, .end), { bytes := artifactBytes, pos := 615, limit := 615 }) := by
  cbv

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 566, limit := 19083 } = .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 615, limit := 19083 }) := by
  refine code_eq_of_parts (size := 48)
    (payload := { bytes := artifactBytes, pos := 567, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 570, limit := 615 })
    (bodyFinish := { bytes := artifactBytes, pos := 615, limit := 615 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_1_tail0
  · rfl

#print axioms code1_decoded

end Project.Gpt2CachedStep.Artifact
