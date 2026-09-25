import Project.EulerOutwardGrid.ArtifactByteLookup
import Project.EulerOutwardGrid.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerOutwardGrid.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_45_23_t_0_t_tail74 :
    instructionSequenceAt 220 false { bytes := artifactBytes, pos := 4747, limit := 4891 } =
      .ok ((((((((Cache.raw.codes[45]!).body)[23]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 4877, limit := 4891 }) := by
  cbv

@[cbv_eval] theorem sequence_45_23_t_0_t_tail0 :
    instructionSequenceAt 294 false { bytes := artifactBytes, pos := 4625, limit := 4891 } =
      .ok ((((((((Cache.raw.codes[45]!).body)[23]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4877, limit := 4891 }) := by
  cbv

@[cbv_eval] theorem sequence_45_23_t_tail0 :
    instructionSequenceAt 296 false { bytes := artifactBytes, pos := 4623, limit := 4891 } =
      .ok ((((((Cache.raw.codes[45]!).body)[23]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4878, limit := 4891 }) := by
  cbv

@[cbv_eval] theorem sequence_45_tail23 :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 4621, limit := 4891 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 23, .end), { bytes := artifactBytes, pos := 4891, limit := 4891 }) := by
  cbv

@[cbv_eval] theorem sequence_45_tail0 :
    instructionSequenceAt 321 false { bytes := artifactBytes, pos := 4570, limit := 4891 } =
      .ok ((((Cache.raw.codes[45]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4891, limit := 4891 }) := by
  cbv

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 4565, limit := 5720 } = .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 4891, limit := 5720 }) := by
  refine code_eq_of_parts (size := 324)
    (payload := { bytes := artifactBytes, pos := 4567, limit := 5720 })
    (bodyStart := { bytes := artifactBytes, pos := 4570, limit := 4891 })
    (bodyFinish := { bytes := artifactBytes, pos := 4891, limit := 4891 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_45_tail0
  · rfl

#print axioms code45_decoded

end Project.EulerOutwardGrid.Artifact
