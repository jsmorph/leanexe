import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_28_t_0_t_tail18 :
    instructionSequenceAt 4258 false { bytes := artifactBytes, pos := 17327, limit := 18733 } =
      .ok ((((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 17455, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_28_t_0_t_tail0 :
    instructionSequenceAt 4276 false { bytes := artifactBytes, pos := 17296, limit := 18733 } =
      .ok ((((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17455, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_28_t_0_t_tail18 :
    instructionSequenceAt 4194 false { bytes := artifactBytes, pos := 17941, limit := 18733 } =
      .ok ((((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 18069, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_28_t_0_t_tail0 :
    instructionSequenceAt 4212 false { bytes := artifactBytes, pos := 17910, limit := 18733 } =
      .ok ((((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18069, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_28_t_tail0 :
    instructionSequenceAt 4278 false { bytes := artifactBytes, pos := 17294, limit := 18733 } =
      .ok ((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17456, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_32_t_tail8 :
    instructionSequenceAt 4266 true { bytes := artifactBytes, pos := 17476, limit := 18733 } =
      .ok ((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17607, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_32_t_tail0 :
    instructionSequenceAt 4274 true { bytes := artifactBytes, pos := 17463, limit := 18733 } =
      .ok ((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17607, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_28_t_tail0 :
    instructionSequenceAt 4214 false { bytes := artifactBytes, pos := 17908, limit := 18733 } =
      .ok ((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18070, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
