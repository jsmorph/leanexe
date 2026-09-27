import Project.EulerReconstructed.ArtifactCodes104To111Part1
import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code110_decoded :
    code { bytes := artifactBytes, pos := 16357, limit := 30726 } =
      .ok (Cache.raw.codes[110]!, { bytes := artifactBytes, pos := 16386, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 16358, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16361, limit := 16386 })
    (bodyFinish := { bytes := artifactBytes, pos := 16386, limit := 16386 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code110_seq_110_tail0_decoded
  · rfl

#print axioms code110_decoded

@[cbv_eval] theorem code111_seq_111_tail0_decoded :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 16390, limit := 16415 } =
      .ok ((((Cache.raw.codes[111]!).body).drop 0, .end), { bytes := artifactBytes, pos := 16415, limit := 16415 }) := by
  cbv

theorem code111_decoded :
    code { bytes := artifactBytes, pos := 16386, limit := 30726 } =
      .ok (Cache.raw.codes[111]!, { bytes := artifactBytes, pos := 16415, limit := 30726 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 16387, limit := 30726 })
    (bodyStart := { bytes := artifactBytes, pos := 16390, limit := 16415 })
    (bodyFinish := { bytes := artifactBytes, pos := 16415, limit := 16415 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code111_seq_111_tail0_decoded
  · rfl

#print axioms code111_decoded
end Project.EulerReconstructed.Artifact
