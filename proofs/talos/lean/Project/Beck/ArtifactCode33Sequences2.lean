import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode33Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_53_e_54_t_26_t_tail0 :
    instructionSequenceAt 2084 false { bytes := artifactBytes, pos := 20209, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false)[26]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20371, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_30_t_tail8 :
    instructionSequenceAt 2072 true { bytes := artifactBytes, pos := 20391, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false)[30]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 20522, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_30_t_tail0 :
    instructionSequenceAt 2080 true { bytes := artifactBytes, pos := 20378, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20522, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_28_t_tail0 :
    instructionSequenceAt 2082 false { bytes := artifactBytes, pos := 20605, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20767, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_32_t_tail8 :
    instructionSequenceAt 2070 true { bytes := artifactBytes, pos := 20787, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 20918, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_32_t_tail0 :
    instructionSequenceAt 2078 true { bytes := artifactBytes, pos := 20774, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20918, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_tail0 :
    instructionSequenceAt 2051 false { bytes := artifactBytes, pos := 20971, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 21661, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_26_t_tail0 :
    instructionSequenceAt 2140 false { bytes := artifactBytes, pos := 19698, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody false)[26]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19860, limit := 21750 }) := by
  cbv


end Project.Beck.Artifact
