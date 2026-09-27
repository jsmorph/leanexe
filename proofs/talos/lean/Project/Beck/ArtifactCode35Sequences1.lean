import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_148_e_24_t_0_t_tail0 :
    instructionSequenceAt 2954 false { bytes := artifactBytes, pos := 25032, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 25191, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_tail88 :
    instructionSequenceAt 2807 false { bytes := artifactBytes, pos := 25950, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false).drop 88, .end), { bytes := artifactBytes, pos := 26119, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_tail75 :
    instructionSequenceAt 2820 false { bytes := artifactBytes, pos := 25781, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := artifactBytes, pos := 26119, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_tail71 :
    instructionSequenceAt 2824 false { bytes := artifactBytes, pos := 25612, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false).drop 71, .end), { bytes := artifactBytes, pos := 26119, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_tail19 :
    instructionSequenceAt 2876 false { bytes := artifactBytes, pos := 25482, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false).drop 19, .end), { bytes := artifactBytes, pos := 26119, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_148_e_83_t_0_t_tail0 :
    instructionSequenceAt 2895 false { bytes := artifactBytes, pos := 25446, limit := 26239 } =
      .ok ((((((((((((Cache.raw.codes[35]!).body)[40]!).childBody true)[148]!).childBody true)[83]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 26119, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_24_t_0_t_tail18 :
    instructionSequenceAt 3086 false { bytes := artifactBytes, pos := 23239, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 23367, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_t_24_t_0_t_tail0 :
    instructionSequenceAt 3104 false { bytes := artifactBytes, pos := 23208, limit := 26239 } =
      .ok ((((((((((Cache.raw.codes[35]!).body)[40]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23367, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
