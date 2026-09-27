import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_41_tail0 :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 18653, limit := 18730 } =
      .ok ((((Cache.raw.codes[41]!).body).drop 0, .end), { bytes := artifactBytes, pos := 18730, limit := 18730 }) := by
  cbv

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 18649, limit := 19083 } = .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 18730, limit := 19083 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 18650, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 18653, limit := 18730 })
    (bodyFinish := { bytes := artifactBytes, pos := 18730, limit := 18730 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_41_tail0
  · rfl

#print axioms code41_decoded

end Project.Gpt2CachedStep.Artifact
