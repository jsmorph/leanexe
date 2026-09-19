import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_24_tail11 :
    instructionSequenceAt 160 false { bytes := artifactBytes, pos := 5684, limit := 5824 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 11, .end), { bytes := artifactBytes, pos := 5824, limit := 5824 }) := by
  cbv

@[cbv_eval] theorem sequence_24_tail0 :
    instructionSequenceAt 171 false { bytes := artifactBytes, pos := 5653, limit := 5824 } =
      .ok ((((Cache.raw.codes[24]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5824, limit := 5824 }) := by
  cbv

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 5648, limit := 19083 } = .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 5824, limit := 19083 }) := by
  refine code_eq_of_parts (size := 174)
    (payload := { bytes := artifactBytes, pos := 5650, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 5653, limit := 5824 })
    (bodyFinish := { bytes := artifactBytes, pos := 5824, limit := 5824 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_24_tail0
  · rfl

#print axioms code24_decoded

end Project.Gpt2CachedStep.Artifact
