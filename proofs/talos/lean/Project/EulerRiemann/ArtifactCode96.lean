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

@[cbv_eval] theorem code96_seq_96_4_t_tail55_decoded :
    instructionSequenceAt 1020 true { bytes := artifactBytes, pos := 16729, limit := 17501 } =
      .ok ((((((Cache.raw.codes[96]!).body)[4]!).childBody false).drop 55, .otherwise), { bytes := artifactBytes, pos := 17103, limit := 17501 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_4_t_tail11_decoded :
    instructionSequenceAt 1064 true { bytes := artifactBytes, pos := 16460, limit := 17501 } =
      .ok ((((((Cache.raw.codes[96]!).body)[4]!).childBody false).drop 11, .otherwise), { bytes := artifactBytes, pos := 17103, limit := 17501 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_4_t_tail0_decoded :
    instructionSequenceAt 1075 true { bytes := artifactBytes, pos := 16439, limit := 17501 } =
      .ok ((((((Cache.raw.codes[96]!).body)[4]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 17103, limit := 17501 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_4_e_tail24_decoded :
    instructionSequenceAt 1051 false { bytes := artifactBytes, pos := 17149, limit := 17501 } =
      .ok ((((((Cache.raw.codes[96]!).body)[4]!).childBody true).drop 24, .end), { bytes := artifactBytes, pos := 17496, limit := 17501 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_4_e_tail0_decoded :
    instructionSequenceAt 1075 false { bytes := artifactBytes, pos := 17103, limit := 17501 } =
      .ok ((((((Cache.raw.codes[96]!).body)[4]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 17496, limit := 17501 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_tail4_decoded :
    instructionSequenceAt 1077 false { bytes := artifactBytes, pos := 16437, limit := 17501 } =
      .ok ((((Cache.raw.codes[96]!).body).drop 4, .end), { bytes := artifactBytes, pos := 17501, limit := 17501 }) := by
  cbv

@[cbv_eval] theorem code96_seq_96_tail0_decoded :
    instructionSequenceAt 1081 false { bytes := artifactBytes, pos := 16420, limit := 17501 } =
      .ok ((((Cache.raw.codes[96]!).body).drop 0, .end), { bytes := artifactBytes, pos := 17501, limit := 17501 }) := by
  cbv

theorem code96_decoded :
    code { bytes := artifactBytes, pos := 16415, limit := 21767 } =
      .ok (Cache.raw.codes[96]!, { bytes := artifactBytes, pos := 17501, limit := 21767 }) := by
  refine code_eq_of_parts (size := 1084)
    (payload := { bytes := artifactBytes, pos := 16417, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 16420, limit := 17501 })
    (bodyFinish := { bytes := artifactBytes, pos := 17501, limit := 17501 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code96_seq_96_tail0_decoded
  · rfl

#print axioms code96_decoded

end Project.EulerRiemann.Artifact
