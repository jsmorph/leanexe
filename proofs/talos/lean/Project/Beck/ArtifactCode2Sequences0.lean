import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_28_t_0_t_tail18 :
    instructionSequenceAt 817 false { bytes := artifactBytes, pos := 1424, limit := 2025 } =
      .ok ((((((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 1552, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_28_t_0_t_tail0 :
    instructionSequenceAt 835 false { bytes := artifactBytes, pos := 1393, limit := 2025 } =
      .ok ((((((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1552, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_28_t_tail0 :
    instructionSequenceAt 837 false { bytes := artifactBytes, pos := 1391, limit := 2025 } =
      .ok ((((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1553, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_32_t_tail8 :
    instructionSequenceAt 825 true { bytes := artifactBytes, pos := 1573, limit := 2025 } =
      .ok ((((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 1704, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_32_t_tail0 :
    instructionSequenceAt 833 true { bytes := artifactBytes, pos := 1560, limit := 2025 } =
      .ok ((((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1704, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_tail32 :
    instructionSequenceAt 835 true { bytes := artifactBytes, pos := 1558, limit := 2025 } =
      .ok ((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 1802, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_tail28 :
    instructionSequenceAt 839 true { bytes := artifactBytes, pos := 1389, limit := 2025 } =
      .ok ((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 1802, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_35_t_tail0 :
    instructionSequenceAt 867 true { bytes := artifactBytes, pos := 1336, limit := 2025 } =
      .ok ((((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true)[35]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1802, limit := 2025 }) := by
  cbv


end Project.Beck.Artifact
