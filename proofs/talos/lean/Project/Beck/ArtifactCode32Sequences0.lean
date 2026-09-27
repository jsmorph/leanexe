import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_32_14_t_0_t_75_t_7_e_tail11 :
    instructionSequenceAt 619 false { bytes := artifactBytes, pos := 19273, limit := 19522 } =
      .ok ((((((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false)[75]!).childBody false)[7]!).childBody true).drop 11, .end), { bytes := artifactBytes, pos := 19410, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_75_t_7_e_tail0 :
    instructionSequenceAt 630 false { bytes := artifactBytes, pos := 19252, limit := 19522 } =
      .ok ((((((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false)[75]!).childBody false)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 19410, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_41_t_tail20 :
    instructionSequenceAt 653 true { bytes := artifactBytes, pos := 18993, limit := 19522 } =
      .ok ((((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false)[41]!).childBody false).drop 20, .otherwise), { bytes := artifactBytes, pos := 19122, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_41_t_tail0 :
    instructionSequenceAt 673 true { bytes := artifactBytes, pos := 18934, limit := 19522 } =
      .ok ((((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false)[41]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 19122, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_75_t_tail7 :
    instructionSequenceAt 632 true { bytes := artifactBytes, pos := 19247, limit := 19522 } =
      .ok ((((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 7, .otherwise), { bytes := artifactBytes, pos := 19442, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_75_t_tail0 :
    instructionSequenceAt 639 true { bytes := artifactBytes, pos := 19230, limit := 19522 } =
      .ok ((((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false)[75]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 19442, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_tail75 :
    instructionSequenceAt 641 false { bytes := artifactBytes, pos := 19228, limit := 19522 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false).drop 75, .end), { bytes := artifactBytes, pos := 19492, limit := 19522 }) := by
  cbv

@[cbv_eval] theorem sequence_32_14_t_0_t_tail41 :
    instructionSequenceAt 675 false { bytes := artifactBytes, pos := 18932, limit := 19522 } =
      .ok ((((((((Cache.raw.codes[32]!).body)[14]!).childBody false)[0]!).childBody false).drop 41, .end), { bytes := artifactBytes, pos := 19492, limit := 19522 }) := by
  cbv


end Project.Beck.Artifact
