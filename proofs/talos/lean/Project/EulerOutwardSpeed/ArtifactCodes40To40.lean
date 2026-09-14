import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code40_seq_40_tail43_decoded :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 4776, limit := 4936 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 43, .end), { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 4647, limit := 4936 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 25, .end), { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  cbv

@[cbv_eval] theorem code40_seq_40_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 4588, limit := 4936 } =
      .ok ((((Cache.raw.codes[40]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  cbv

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 4583, limit := 4936 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 4936, limit := 4936 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 4585, limit := 4936 })
    (bodyStart := { bytes := artifactBytes, pos := 4588, limit := 4936 })
    (bodyFinish := { bytes := artifactBytes, pos := 4936, limit := 4936 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code40_seq_40_tail0_decoded
  · rfl

#print axioms code40_decoded

end Project.EulerOutwardSpeed.Artifact
