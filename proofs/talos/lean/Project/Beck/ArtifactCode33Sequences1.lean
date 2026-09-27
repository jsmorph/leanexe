import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode33Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_53_e_54_e_28_t_0_t_tail0 :
    instructionSequenceAt 2080 false { bytes := artifactBytes, pos := 20607, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20766, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_tail91 :
    instructionSequenceAt 1958 false { bytes := artifactBytes, pos := 21491, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false).drop 91, .end), { bytes := artifactBytes, pos := 21660, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_tail78 :
    instructionSequenceAt 1971 false { bytes := artifactBytes, pos := 21322, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false).drop 78, .end), { bytes := artifactBytes, pos := 21660, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_tail74 :
    instructionSequenceAt 1975 false { bytes := artifactBytes, pos := 21153, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 21660, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_tail21 :
    instructionSequenceAt 2028 false { bytes := artifactBytes, pos := 21013, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 21660, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_59_t_0_t_tail0 :
    instructionSequenceAt 2049 false { bytes := artifactBytes, pos := 20973, limit := 21750 } =
      .ok ((((((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true)[59]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 21660, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_26_t_0_t_tail18 :
    instructionSequenceAt 2120 false { bytes := artifactBytes, pos := 19731, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 19859, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_26_t_0_t_tail0 :
    instructionSequenceAt 2138 false { bytes := artifactBytes, pos := 19700, limit := 21750 } =
      .ok ((((((((((Cache.raw.codes[33]!).body)[53]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 19859, limit := 21750 }) := by
  cbv


end Project.Beck.Artifact
