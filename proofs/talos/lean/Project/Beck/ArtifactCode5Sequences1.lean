import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode5Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_44_t_tail8 :
    instructionSequenceAt 1504 true { bytes := artifactBytes, pos := 2562, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[44]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 2693, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_44_t_tail0 :
    instructionSequenceAt 1512 true { bytes := artifactBytes, pos := 2549, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[44]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 2693, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_tail116 :
    instructionSequenceAt 1362 false { bytes := artifactBytes, pos := 3498, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true).drop 116, .end), { bytes := artifactBytes, pos := 3632, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_tail85 :
    instructionSequenceAt 1393 false { bytes := artifactBytes, pos := 3351, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true).drop 85, .end), { bytes := artifactBytes, pos := 3632, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_tail69 :
    instructionSequenceAt 1409 false { bytes := artifactBytes, pos := 3126, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true).drop 69, .end), { bytes := artifactBytes, pos := 3632, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_tail65 :
    instructionSequenceAt 1413 false { bytes := artifactBytes, pos := 2957, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true).drop 65, .end), { bytes := artifactBytes, pos := 3632, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_tail2 :
    instructionSequenceAt 1476 false { bytes := artifactBytes, pos := 2828, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true).drop 2, .end), { bytes := artifactBytes, pos := 3632, limit := 3678 }) := by
  cbv

@[cbv_eval] theorem sequence_5_6_t_0_t_14_e_34_e_78_e_tail0 :
    instructionSequenceAt 1478 false { bytes := artifactBytes, pos := 2824, limit := 3678 } =
      .ok ((((((((((((((Cache.raw.codes[5]!).body)[6]!).childBody false)[0]!).childBody false)[14]!).childBody true)[34]!).childBody true)[78]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 3632, limit := 3678 }) := by
  cbv


end Project.Beck.Artifact
