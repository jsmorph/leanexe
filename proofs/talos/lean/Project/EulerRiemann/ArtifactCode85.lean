import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code85_seq_85_4_t_0_t_19_e_23_t_tail1_decoded :
    instructionSequenceAt 445 true { bytes := artifactBytes, pos := 11795, limit := 12150 } =
      .ok ((((((((((((Cache.raw.codes[85]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 1, .otherwise), { bytes := artifactBytes, pos := 12052, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_4_t_0_t_19_e_23_t_tail0_decoded :
    instructionSequenceAt 446 true { bytes := artifactBytes, pos := 11793, limit := 12150 } =
      .ok ((((((((((((Cache.raw.codes[85]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true)[23]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 12052, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_4_t_0_t_19_e_tail23_decoded :
    instructionSequenceAt 448 false { bytes := artifactBytes, pos := 11791, limit := 12150 } =
      .ok ((((((((((Cache.raw.codes[85]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 23, .end), { bytes := artifactBytes, pos := 12074, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_4_t_0_t_19_e_tail0_decoded :
    instructionSequenceAt 471 false { bytes := artifactBytes, pos := 11737, limit := 12150 } =
      .ok ((((((((((Cache.raw.codes[85]!).body)[4]!).childBody false)[0]!).childBody false)[19]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 12074, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_4_t_0_t_tail19_decoded :
    instructionSequenceAt 473 false { bytes := artifactBytes, pos := 11714, limit := 12150 } =
      .ok ((((((((Cache.raw.codes[85]!).body)[4]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 12077, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_4_t_0_t_tail0_decoded :
    instructionSequenceAt 492 false { bytes := artifactBytes, pos := 11662, limit := 12150 } =
      .ok ((((((((Cache.raw.codes[85]!).body)[4]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12077, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_4_t_tail0_decoded :
    instructionSequenceAt 494 false { bytes := artifactBytes, pos := 11660, limit := 12150 } =
      .ok ((((((Cache.raw.codes[85]!).body)[4]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 12078, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_tail4_decoded :
    instructionSequenceAt 496 false { bytes := artifactBytes, pos := 11658, limit := 12150 } =
      .ok ((((Cache.raw.codes[85]!).body).drop 4, .end), { bytes := artifactBytes, pos := 12150, limit := 12150 }) := by
  cbv

@[cbv_eval] theorem code85_seq_85_tail0_decoded :
    instructionSequenceAt 500 false { bytes := artifactBytes, pos := 11650, limit := 12150 } =
      .ok ((((Cache.raw.codes[85]!).body).drop 0, .end), { bytes := artifactBytes, pos := 12150, limit := 12150 }) := by
  cbv

theorem code85_decoded :
    code { bytes := artifactBytes, pos := 11645, limit := 21767 } =
      .ok (Cache.raw.codes[85]!, { bytes := artifactBytes, pos := 12150, limit := 21767 }) := by
  refine code_eq_of_parts (size := 503)
    (payload := { bytes := artifactBytes, pos := 11647, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 11650, limit := 12150 })
    (bodyFinish := { bytes := artifactBytes, pos := 12150, limit := 12150 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code85_seq_85_tail0_decoded
  · rfl

#print axioms code85_decoded

end Project.EulerRiemann.Artifact
