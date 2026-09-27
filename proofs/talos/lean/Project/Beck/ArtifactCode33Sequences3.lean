import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode33Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_53_t_30_t_tail8 :
    instructionSequenceAt 2128 true { bytes := artifactBytes, pos := 19880, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody false)[30]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 20011, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_30_t_tail0 :
    instructionSequenceAt 2136 true { bytes := artifactBytes, pos := 19867, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody false)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20011, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_tail30 :
    instructionSequenceAt 2082 true { bytes := artifactBytes, pos := 20376, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false).drop 30, .otherwise), { bytes := artifactBytes, pos := 20550, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_tail26 :
    instructionSequenceAt 2086 true { bytes := artifactBytes, pos := 20207, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 20550, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_t_tail0 :
    instructionSequenceAt 2112 true { bytes := artifactBytes, pos := 20157, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 20550, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_tail59 :
    instructionSequenceAt 2053 false { bytes := artifactBytes, pos := 20969, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true).drop 59, .end), { bytes := artifactBytes, pos := 21716, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_tail32 :
    instructionSequenceAt 2080 false { bytes := artifactBytes, pos := 20772, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true).drop 32, .end), { bytes := artifactBytes, pos := 21716, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_54_e_tail28 :
    instructionSequenceAt 2084 false { bytes := artifactBytes, pos := 20603, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 21716, limit := 21750 }) := by
  cbv


end Project.Beck.Artifact
