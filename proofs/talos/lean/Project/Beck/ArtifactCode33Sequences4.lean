import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode33Sequences3

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_33_53_e_54_e_tail0 :
    instructionSequenceAt 2112 false { bytes := artifactBytes, pos := 20550, limit := 21750 } =
      .ok ((((((((Cache.raw.codes[33]!).body)[53]!).childBody true)[54]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 21716, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_tail30 :
    instructionSequenceAt 2138 true { bytes := artifactBytes, pos := 19865, limit := 21750 } =
      .ok ((((((Cache.raw.codes[33]!).body)[53]!).childBody false).drop 30, .otherwise), { bytes := artifactBytes, pos := 20039, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_tail26 :
    instructionSequenceAt 2142 true { bytes := artifactBytes, pos := 19696, limit := 21750 } =
      .ok ((((((Cache.raw.codes[33]!).body)[53]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 20039, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_t_tail0 :
    instructionSequenceAt 2168 true { bytes := artifactBytes, pos := 19646, limit := 21750 } =
      .ok ((((((Cache.raw.codes[33]!).body)[53]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 20039, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_tail54 :
    instructionSequenceAt 2114 false { bytes := artifactBytes, pos := 20155, limit := 21750 } =
      .ok ((((((Cache.raw.codes[33]!).body)[53]!).childBody true).drop 54, .end), { bytes := artifactBytes, pos := 21717, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_53_e_tail0 :
    instructionSequenceAt 2168 false { bytes := artifactBytes, pos := 20039, limit := 21750 } =
      .ok ((((((Cache.raw.codes[33]!).body)[53]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 21717, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail53 :
    instructionSequenceAt 2170 false { bytes := artifactBytes, pos := 19644, limit := 21750 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 53, .end), { bytes := artifactBytes, pos := 21750, limit := 21750 }) := by
  cbv

@[cbv_eval] theorem sequence_33_tail0 :
    instructionSequenceAt 2223 false { bytes := artifactBytes, pos := 19527, limit := 21750 } =
      .ok ((((Cache.raw.codes[33]!).body).drop 0, .end), { bytes := artifactBytes, pos := 21750, limit := 21750 }) := by
  cbv


end Project.Beck.Artifact
