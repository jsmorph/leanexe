import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_71_t_0_t_tail18 :
    instructionSequenceAt 2802 false { bytes := artifactBytes, pos := 25647, limit := 26239 } =
      .ok ((((((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false)[71]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 25775, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_71_t_0_t_tail0 :
    instructionSequenceAt 2820 false { bytes := artifactBytes, pos := 25616, limit := 26239 } =
      .ok ((((((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false)[71]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25775, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_71_t_tail0 :
    instructionSequenceAt 2822 false { bytes := artifactBytes, pos := 25614, limit := 26239 } =
      .ok ((((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false)[71]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25776, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_75_t_tail8 :
    instructionSequenceAt 2810 true { bytes := artifactBytes, pos := 25796, limit := 26239 } =
      .ok ((((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 25927, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_75_t_tail0 :
    instructionSequenceAt 2818 true { bytes := artifactBytes, pos := 25783, limit := 26239 } =
      .ok ((((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25927, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_24_t_0_t_tail18 :
    instructionSequenceAt 2936 false { bytes := artifactBytes, pos := 24646, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 24774, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_t_24_t_0_t_tail0 :
    instructionSequenceAt 2954 false { bytes := artifactBytes, pos := 24615, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 24774, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_24_t_0_t_tail18 :
    instructionSequenceAt 2936 false { bytes := artifactBytes, pos := 25063, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 25191, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
