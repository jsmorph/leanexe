import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Evaluate

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code107_tail34_decoded :
    instructionSequenceAt 314 false { bytes := artifactBytes, pos := 21509, limit := 21767 } =
      .ok (((Cache.raw.codes[107]!).body.drop 34, .end),
        { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  cbv

@[cbv_eval] theorem code107_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 21419, limit := 21767 } =
      .ok (((Cache.raw.codes[107]!).body.drop 0, .end),
        { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  cbv

theorem code107_decoded :
    code { bytes := artifactBytes, pos := 21414, limit := 21767 } =
      .ok (Cache.raw.codes[107]!, { bytes := artifactBytes, pos := 21767, limit := 21767 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 21416, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 21419, limit := 21767 })
    (bodyFinish := { bytes := artifactBytes, pos := 21767, limit := 21767 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code107_tail0_decoded
  · rfl

#print axioms code107_decoded

end Project.EulerRiemann.Artifact
