import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_40_tail0 :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 18623, limit := 18649 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18649, limit := 18649 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 18621, limit := 19083 } = .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 18649, limit := 19083 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 18622, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 18623, limit := 18649 })
    (bodyFinish := { bytes := artifactBytes, pos := 18649, limit := 18649 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_40_tail0
  · rfl

#print axioms code40_decoded

end Project.Gpt2CachedStep.Artifact
