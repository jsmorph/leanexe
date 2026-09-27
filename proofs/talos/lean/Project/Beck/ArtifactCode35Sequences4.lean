import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences3

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_50_t_tail0 :
    instructionSequenceAt 3080 true { bytes := artifactBytes, pos := 23836, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[50]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23980, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_98_t_tail0 :
    instructionSequenceAt 3032 false { bytes := artifactBytes, pos := 24113, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[98]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24275, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_102_t_tail8 :
    instructionSequenceAt 3020 true { bytes := artifactBytes, pos := 24295, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[102]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 24426, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_102_t_tail0 :
    instructionSequenceAt 3028 true { bytes := artifactBytes, pos := 24282, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[102]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24426, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_tail28 :
    instructionSequenceAt 2954 true { bytes := artifactBytes, pos := 24780, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 24982, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_tail24 :
    instructionSequenceAt 2958 true { bytes := artifactBytes, pos := 24611, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false).drop 24, .otherwise), { bytes := artifactBytes, pos := 24982, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_tail0 :
    instructionSequenceAt 2982 true { bytes := artifactBytes, pos := 24565, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 24982, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_tail83 :
    instructionSequenceAt 2899 false { bytes := artifactBytes, pos := 25442, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true).drop 83, .end), { bytes := artifactBytes, pos := 26171, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
