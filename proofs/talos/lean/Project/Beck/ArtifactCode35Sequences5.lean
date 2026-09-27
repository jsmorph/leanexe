import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences4

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_148_e_tail28 :
    instructionSequenceAt 2954 false { bytes := artifactBytes, pos := 25197, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true).drop 28, .end), { bytes := artifactBytes, pos := 26171, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_tail24 :
    instructionSequenceAt 2958 false { bytes := artifactBytes, pos := 25028, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true).drop 24, .end), { bytes := artifactBytes, pos := 26171, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_tail0 :
    instructionSequenceAt 2982 false { bytes := artifactBytes, pos := 24982, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 26171, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_tail28 :
    instructionSequenceAt 3104 true { bytes := artifactBytes, pos := 23373, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 23575, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_tail24 :
    instructionSequenceAt 3108 true { bytes := artifactBytes, pos := 23204, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody false).drop 24, .otherwise), { bytes := artifactBytes, pos := 23575, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_tail0 :
    instructionSequenceAt 3132 true { bytes := artifactBytes, pos := 23158, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 23575, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail148 :
    instructionSequenceAt 2984 false { bytes := artifactBytes, pos := 24563, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 148, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail108 :
    instructionSequenceAt 3024 false { bytes := artifactBytes, pos := 24435, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 108, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
