import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code48_seq_48_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 5298, limit := 5375 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5375, limit := 5375 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 5294, limit := 5728 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 5375, limit := 5728 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 5295, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 5298, limit := 5375 })
    (bodyFinish := { bytes := artifactBytes, pos := 5375, limit := 5375 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code48_seq_48_tail0_decoded
  · rfl

#print axioms code48_decoded

@[cbv_eval] theorem code49_seq_49_tail44_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 5694, limit := 5728 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 44, .end), { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  cbv

@[cbv_eval] theorem code49_seq_49_tail42_decoded :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 5567, limit := 5728 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 42, .end), { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  cbv

@[cbv_eval] theorem code49_seq_49_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 5439, limit := 5728 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 25, .end), { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  cbv

@[cbv_eval] theorem code49_seq_49_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 5380, limit := 5728 } =
      .ok ((((Cache.raw.codes[49]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  cbv

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 5375, limit := 5728 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 5728, limit := 5728 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 5377, limit := 5728 })
    (bodyStart := { bytes := artifactBytes, pos := 5380, limit := 5728 })
    (bodyFinish := { bytes := artifactBytes, pos := 5728, limit := 5728 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code49_seq_49_tail0_decoded
  · rfl

#print axioms code49_decoded


end Project.EulerOutwardGrid.Artifact
