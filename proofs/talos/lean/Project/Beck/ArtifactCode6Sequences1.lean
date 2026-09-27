import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode6Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_7_e_20_e_105_t_tail8 :
    instructionSequenceAt 1177 true { bytes := artifactBytes, pos := 4631, limit := 5006 } =
      .ok ((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[105]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 4762, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_105_t_tail0 :
    instructionSequenceAt 1185 true { bytes := artifactBytes, pos := 4618, limit := 5006 } =
      .ok ((((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true)[105]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 4762, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_tail137 :
    instructionSequenceAt 1155 false { bytes := artifactBytes, pos := 4822, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 137, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_tail105 :
    instructionSequenceAt 1187 false { bytes := artifactBytes, pos := 4616, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 105, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_tail101 :
    instructionSequenceAt 1191 false { bytes := artifactBytes, pos := 4447, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 101, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_tail62 :
    instructionSequenceAt 1230 false { bytes := artifactBytes, pos := 4228, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 62, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_tail58 :
    instructionSequenceAt 1234 false { bytes := artifactBytes, pos := 4059, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 58, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_20_e_tail9 :
    instructionSequenceAt 1283 false { bytes := artifactBytes, pos := 3922, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 9, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv


end Project.Beck.Artifact
