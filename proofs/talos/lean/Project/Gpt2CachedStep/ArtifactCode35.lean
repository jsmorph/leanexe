import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_tail0 :
    instructionSequenceAt 19 false { bytes := artifactBytes, pos := 14585, limit := 14604 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14604, limit := 14604 }) := by
  cbv

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 14581, limit := 19083 } = .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 14604, limit := 19083 }) := by
  refine code_eq_of_parts (size := 22)
    (payload := { bytes := artifactBytes, pos := 14582, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 14585, limit := 14604 })
    (bodyFinish := { bytes := artifactBytes, pos := 14604, limit := 14604 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_35_tail0
  · rfl

#print axioms code35_decoded

end Project.Gpt2CachedStep.Artifact
