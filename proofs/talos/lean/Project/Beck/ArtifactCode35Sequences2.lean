import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_46_t_0_t_tail18 :
    instructionSequenceAt 3064 false { bytes := artifactBytes, pos := 23700, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[46]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 23828, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_46_t_0_t_tail0 :
    instructionSequenceAt 3082 false { bytes := artifactBytes, pos := 23669, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[46]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23828, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_98_t_0_t_tail18 :
    instructionSequenceAt 3012 false { bytes := artifactBytes, pos := 24146, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[98]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 24274, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_98_t_0_t_tail0 :
    instructionSequenceAt 3030 false { bytes := artifactBytes, pos := 24115, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[98]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24274, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_24_t_tail0 :
    instructionSequenceAt 2956 false { bytes := artifactBytes, pos := 24613, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24775, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_28_t_tail8 :
    instructionSequenceAt 2944 true { bytes := artifactBytes, pos := 24795, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 24926, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_28_t_tail0 :
    instructionSequenceAt 2952 true { bytes := artifactBytes, pos := 24782, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24926, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_24_t_tail0 :
    instructionSequenceAt 2956 false { bytes := artifactBytes, pos := 25030, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25192, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
