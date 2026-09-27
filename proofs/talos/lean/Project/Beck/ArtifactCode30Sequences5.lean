import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences4

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_288_t_28_t_tail0 :
    instructionSequenceAt 4394 true { bytes := artifactBytes, pos := 16030, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16174, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_30_t_tail0 :
    instructionSequenceAt 4392 false { bytes := artifactBytes, pos := 16266, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16428, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_34_t_tail8 :
    instructionSequenceAt 4380 true { bytes := artifactBytes, pos := 16448, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[34]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16579, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_34_t_tail0 :
    instructionSequenceAt 4388 true { bytes := artifactBytes, pos := 16435, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[34]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16579, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_tail32 :
    instructionSequenceAt 4325 true { bytes := artifactBytes, pos := 16901, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 17145, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_tail28 :
    instructionSequenceAt 4329 true { bytes := artifactBytes, pos := 16732, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 17145, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_tail0 :
    instructionSequenceAt 4357 true { bytes := artifactBytes, pos := 16679, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 17145, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_tail0 :
    instructionSequenceAt 4337 false { bytes := artifactBytes, pos := 17187, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18475, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
