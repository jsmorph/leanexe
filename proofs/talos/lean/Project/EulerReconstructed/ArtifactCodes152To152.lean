import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code152_seq_152_tail43_decoded :
    instructionSequenceAt 307 false { bytes := artifactBytes, pos := 30565, limit := 30726 } =
      .ok ((((Cache.raw.codes[152]!).body).drop 43, .end), { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  cbv

@[cbv_eval] theorem code152_seq_152_tail26_decoded :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 30437, limit := 30726 } =
      .ok ((((Cache.raw.codes[152]!).body).drop 26, .end), { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  cbv

@[cbv_eval] theorem code152_seq_152_tail0_decoded :
    instructionSequenceAt 350 false { bytes := artifactBytes, pos := 30376, limit := 30726 } =
      .ok ((((Cache.raw.codes[152]!).body).drop 0, .end), { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  cbv

theorem code152_decoded :
    code { bytes := artifactBytes, pos := 30371, limit := 30726 } =
      .ok (Cache.raw.codes[152]!, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by
  refine code_eq_of_parts (size := 353)
    (payload := { bytes := artifactBytes, pos := 30373, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 30376, limit := 30726 })
    (bodyFinish := { bytes := artifactBytes, pos := 30726, limit := 30726 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code152_seq_152_tail0_decoded
  · rfl

#print axioms code152_decoded


end Project.EulerReconstructed.Artifact
