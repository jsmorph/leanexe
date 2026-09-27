import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_17_10_t_0_t_tail53 :
    instructionSequenceAt 428 false { bytes := artifactBytes, pos := 5931, limit := 6140 } =
      .ok ((((((((Cache.raw.codes[17]!).body)[10]!).childBody false)[0]!).childBody false).drop 53, .end), { bytes := artifactBytes, pos := 6124, limit := 6140 }) := by
  cbv

@[cbv_eval] theorem sequence_17_10_t_0_t_tail25 :
    instructionSequenceAt 456 false { bytes := artifactBytes, pos := 5715, limit := 6140 } =
      .ok ((((((((Cache.raw.codes[17]!).body)[10]!).childBody false)[0]!).childBody false).drop 25, .end), { bytes := artifactBytes, pos := 6124, limit := 6140 }) := by
  cbv

@[cbv_eval] theorem sequence_17_10_t_0_t_tail0 :
    instructionSequenceAt 481 false { bytes := artifactBytes, pos := 5669, limit := 6140 } =
      .ok ((((((((Cache.raw.codes[17]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6124, limit := 6140 }) := by
  cbv

@[cbv_eval] theorem sequence_17_10_t_tail0 :
    instructionSequenceAt 483 false { bytes := artifactBytes, pos := 5667, limit := 6140 } =
      .ok ((((((Cache.raw.codes[17]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6125, limit := 6140 }) := by
  cbv

@[cbv_eval] theorem sequence_17_tail10 :
    instructionSequenceAt 485 false { bytes := artifactBytes, pos := 5665, limit := 6140 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 10, .end), { bytes := artifactBytes, pos := 6140, limit := 6140 }) := by
  cbv

@[cbv_eval] theorem sequence_17_tail0 :
    instructionSequenceAt 495 false { bytes := artifactBytes, pos := 5645, limit := 6140 } =
      .ok ((((Cache.raw.codes[17]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6140, limit := 6140 }) := by
  cbv

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 5640, limit := 27068 } = .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 6140, limit := 27068 }) := by
  refine code_eq_of_parts (size := 498)
    (payload := { bytes := artifactBytes, pos := 5642, limit := 27068 })
    (bodyStart := { bytes := artifactBytes, pos := 5645, limit := 6140 })
    (bodyFinish := { bytes := artifactBytes, pos := 6140, limit := 6140 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_17_tail0
  · rfl

#print axioms code17_decoded

end Project.Beck.Artifact
