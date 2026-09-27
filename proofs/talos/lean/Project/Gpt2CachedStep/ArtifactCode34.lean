import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 14562, limit := 14581 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14581, limit := 14581 }) := by
  cbv

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 14558, limit := 19083 } = .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 14581, limit := 19083 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 14559, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 14562, limit := 14581 })
    (bodyFinish := { bytes := artifactBytes, pos := 14581, limit := 14581 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_34_tail0
  · rfl

#print axioms code34_decoded

end Project.Gpt2CachedStep.Artifact
