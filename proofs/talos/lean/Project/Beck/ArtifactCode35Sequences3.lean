import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_148_e_28_t_tail8 :
    instructionSequenceAt 2944 true { bytes := artifactBytes, pos := 25212, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 25343, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_28_t_tail0 :
    instructionSequenceAt 2952 true { bytes := artifactBytes, pos := 25199, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25343, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_tail0 :
    instructionSequenceAt 2897 false { bytes := artifactBytes, pos := 25444, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26120, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_24_t_tail0 :
    instructionSequenceAt 3106 false { bytes := artifactBytes, pos := 23206, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23368, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_28_t_tail8 :
    instructionSequenceAt 3094 true { bytes := artifactBytes, pos := 23388, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 23519, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_28_t_tail0 :
    instructionSequenceAt 3102 true { bytes := artifactBytes, pos := 23375, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23519, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_46_t_tail0 :
    instructionSequenceAt 3084 false { bytes := artifactBytes, pos := 23667, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[46]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23829, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_50_t_tail8 :
    instructionSequenceAt 3072 true { bytes := artifactBytes, pos := 23849, limit := 26239 } =
      .ok ((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[50]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 23980, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
