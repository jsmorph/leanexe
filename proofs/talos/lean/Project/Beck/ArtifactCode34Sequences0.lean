import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_26_t_0_t_tail18 :
    instructionSequenceAt 1171 false { bytes := artifactBytes, pos := 22038, limit := 23060 } =
      .ok ((((((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 22166, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_26_t_0_t_tail0 :
    instructionSequenceAt 1189 false { bytes := artifactBytes, pos := 22007, limit := 23060 } =
      .ok ((((((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false)[26]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22166, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_26_t_tail0 :
    instructionSequenceAt 1191 false { bytes := artifactBytes, pos := 22005, limit := 23060 } =
      .ok ((((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false)[26]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22167, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_30_t_tail8 :
    instructionSequenceAt 1179 true { bytes := artifactBytes, pos := 22187, limit := 23060 } =
      .ok ((((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false)[30]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 22318, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_30_t_tail0 :
    instructionSequenceAt 1187 true { bytes := artifactBytes, pos := 22174, limit := 23060 } =
      .ok ((((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22318, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_tail30 :
    instructionSequenceAt 1189 true { bytes := artifactBytes, pos := 22172, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false).drop 30, .otherwise), { bytes := artifactBytes, pos := 22350, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_tail26 :
    instructionSequenceAt 1193 true { bytes := artifactBytes, pos := 22003, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false).drop 26, .otherwise), { bytes := artifactBytes, pos := 22350, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_t_tail0 :
    instructionSequenceAt 1219 true { bytes := artifactBytes, pos := 21953, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 22350, limit := 23060 }) := by
  cbv


end Project.Beck.Artifact
