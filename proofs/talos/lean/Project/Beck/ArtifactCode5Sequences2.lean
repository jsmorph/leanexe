import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode5Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_tail78 :
    instructionSequenceAt 1480 false { bytes := artifactBytes, pos := 2797, limit := 3678 } =
      .ok ((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true).drop 78, .end), { bytes := artifactBytes, pos := 3633, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_tail44 :
    instructionSequenceAt 1514 false { bytes := artifactBytes, pos := 2547, limit := 3678 } =
      .ok ((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true).drop 44, .end), { bytes := artifactBytes, pos := 3633, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_tail40 :
    instructionSequenceAt 1518 false { bytes := artifactBytes, pos := 2378, limit := 3678 } =
      .ok ((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true).drop 40, .end), { bytes := artifactBytes, pos := 3633, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_tail0 :
    instructionSequenceAt 1558 false { bytes := artifactBytes, pos := 2300, limit := 3678 } =
      .ok ((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 3633, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_tail34 :
    instructionSequenceAt 1560 false { bytes := artifactBytes, pos := 2273, limit := 3678 } =
      .ok ((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 34, .end), { bytes := artifactBytes, pos := 3634, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_tail5 :
    instructionSequenceAt 1589 false { bytes := artifactBytes, pos := 2144, limit := 3678 } =
      .ok ((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 5, .end), { bytes := artifactBytes, pos := 3634, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_tail0 :
    instructionSequenceAt 1594 false { bytes := artifactBytes, pos := 2134, limit := 3678 } =
      .ok ((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 3634, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_tail14 :
    instructionSequenceAt 1596 false { bytes := artifactBytes, pos := 2107, limit := 3678 } =
      .ok ((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false).drop 14, .end), { bytes := artifactBytes, pos := 3637, limit := 3678 }) := by
  cbv


end Project.Beck.Artifact
