import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode2Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_tail50 :
    instructionSequenceAt 854 false { bytes := artifactBytes, pos := 1854, limit := 2025 } =
      .ok ((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true).drop 50, .end), { bytes := artifactBytes, pos := 1992, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_tail35 :
    instructionSequenceAt 869 false { bytes := artifactBytes, pos := 1334, limit := 2025 } =
      .ok ((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true).drop 35, .end), { bytes := artifactBytes, pos := 1992, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_24_e_tail0 :
    instructionSequenceAt 904 false { bytes := artifactBytes, pos := 1262, limit := 2025 } =
      .ok ((((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true)[24]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 1992, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_tail24 :
    instructionSequenceAt 906 false { bytes := artifactBytes, pos := 1243, limit := 2025 } =
      .ok ((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true).drop 24, .end), { bytes := artifactBytes, pos := 1993, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_21_e_tail0 :
    instructionSequenceAt 930 false { bytes := artifactBytes, pos := 1164, limit := 2025 } =
      .ok ((((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false)[21]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 1993, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_tail21 :
    instructionSequenceAt 932 false { bytes := artifactBytes, pos := 1145, limit := 2025 } =
      .ok ((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 1996, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_0_t_tail0 :
    instructionSequenceAt 953 false { bytes := artifactBytes, pos := 1078, limit := 2025 } =
      .ok ((((((((Cache.raw.codes[2]!).body)[6]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1996, limit := 2025 }) := by
  cbv

@[cbv_eval] theorem sequence_2_6_t_tail0 :
    instructionSequenceAt 955 false { bytes := artifactBytes, pos := 1076, limit := 2025 } =
      .ok ((((((Cache.raw.codes[2]!).body)[6]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 1997, limit := 2025 }) := by
  cbv


end Project.Beck.Artifact
