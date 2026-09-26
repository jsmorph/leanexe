import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_37_21_t_tail33 :
    instructionSequenceAt 205 true { bytes := artifactBytes, pos := 4160, limit := 4308 } =
      .ok ((((((Cache.raw.codes[37]!).body)[21]!).childBody false).drop 33, .otherwise), { bytes := artifactBytes, pos := 4288, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem sequence_37_21_t_tail0 :
    instructionSequenceAt 238 true { bytes := artifactBytes, pos := 4094, limit := 4308 } =
      .ok ((((((Cache.raw.codes[37]!).body)[21]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 4288, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail21 :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 4092, limit := 4308 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4308, limit := 4308 }) := by
  cbv

@[cbv_eval] theorem sequence_37_tail0 :
    instructionSequenceAt 261 false { bytes := artifactBytes, pos := 4047, limit := 4308 } =
      .ok ((((Cache.raw.codes[37]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4308, limit := 4308 }) := by
  cbv

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4042, limit := 5720 } = .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4308, limit := 5720 }) := by
  refine code_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 4044, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4047, limit := 4308 })
    (bodyFinish := { bytes := artifactBytes, pos := 4308, limit := 4308 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_37_tail0
  · rfl

#print axioms code37_decoded

end Project.EulerOutwardGrid.Artifact
