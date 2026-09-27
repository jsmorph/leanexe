import Project.Gpt2CachedStep.ArtifactByteLookup
import Project.Gpt2CachedStep.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2CachedStep.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_13_tail0 :
    instructionSequenceAt 31 false { bytes := artifactBytes, pos := 1162, limit := 1193 } =
      .ok ((((Cache.raw.codes[13]!).body).drop 0, .end), { bytes := artifactBytes, pos := 1193, limit := 1193 }) := by
  cbv

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 1158, limit := 19083 } = .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 1193, limit := 19083 }) := by
  refine code_eq_of_parts (size := 34)
    (payload := { bytes := artifactBytes, pos := 1159, limit := 19083 })
    (bodyStart := { bytes := artifactBytes, pos := 1162, limit := 1193 })
    (bodyFinish := { bytes := artifactBytes, pos := 1193, limit := 1193 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_13_tail0
  · rfl

#print axioms code13_decoded

end Project.Gpt2CachedStep.Artifact
