import Project.EulerOutwardFlux.ArtifactByteLookup
import Project.EulerOutwardFlux.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardFlux.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code56_seq_56_tail0_decoded :
    instructionSequenceAt 26 false { bytes := artifactBytes, pos := 6715, limit := 6741 } =
      .ok ((((Cache.raw.codes[56]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6741, limit := 6741 }) := by
  cbv

theorem code56_decoded :
    code { bytes := artifactBytes, pos := 6713, limit := 7175 } =
      .ok (Cache.raw.codes[56]!, { bytes := artifactBytes, pos := 6741, limit := 7175 }) := by
  refine code_eq_of_parts (size := 27)
    (payload := { bytes := artifactBytes, pos := 6714, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 6715, limit := 6741 })
    (bodyFinish := { bytes := artifactBytes, pos := 6741, limit := 6741 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code56_seq_56_tail0_decoded
  · rfl

#print axioms code56_decoded

@[cbv_eval] theorem code57_seq_57_tail0_decoded :
    instructionSequenceAt 77 false { bytes := artifactBytes, pos := 6745, limit := 6822 } =
      .ok ((((Cache.raw.codes[57]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6822, limit := 6822 }) := by
  cbv

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 6741, limit := 7175 } =
      .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 6822, limit := 7175 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 6742, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 6745, limit := 6822 })
    (bodyFinish := { bytes := artifactBytes, pos := 6822, limit := 6822 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code57_seq_57_tail0_decoded
  · rfl

#print axioms code57_decoded

@[cbv_eval] theorem code58_seq_58_tail44_decoded :
    instructionSequenceAt 304 false { bytes := artifactBytes, pos := 7141, limit := 7175 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 44, .end), { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  cbv

@[cbv_eval] theorem code58_seq_58_tail42_decoded :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 7014, limit := 7175 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 42, .end), { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  cbv

@[cbv_eval] theorem code58_seq_58_tail25_decoded :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 6886, limit := 7175 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 25, .end), { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  cbv

@[cbv_eval] theorem code58_seq_58_tail0_decoded :
    instructionSequenceAt 348 false { bytes := artifactBytes, pos := 6827, limit := 7175 } =
      .ok ((((Cache.raw.codes[58]!).body).drop 0, .end), { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  cbv

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 6822, limit := 7175 } =
      .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 7175, limit := 7175 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 6824, limit := 7175 })
    (bodyStart := { bytes := artifactBytes, pos := 6827, limit := 7175 })
    (bodyFinish := { bytes := artifactBytes, pos := 7175, limit := 7175 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code58_seq_58_tail0_decoded
  · rfl

#print axioms code58_decoded


end Project.EulerOutwardFlux.Artifact
