import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_4_tail0 :
    instructionSequenceAt 68 false { bytes := artifactBytes, pos := 702, limit := 770 } =
      .ok ((((Cache.raw.codes[4]!).body).drop 0, .end), { bytes := artifactBytes, pos := 770, limit := 770 }) := by
  cbv

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 698, limit := 19083 } = .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 770, limit := 19083 }) := by
  refine code_eq_of_parts (size := 71)
    (payload := { bytes := artifactBytes, pos := 699, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 702, limit := 770 })
    (bodyFinish := { bytes := artifactBytes, pos := 770, limit := 770 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_4_tail0
  · rfl

#print axioms code4_decoded

end Project.Gpt2CachedStep.Artifact
