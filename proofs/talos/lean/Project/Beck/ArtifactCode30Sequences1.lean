import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_32_t_tail8 :
    instructionSequenceAt 4202 true { bytes := artifactBytes, pos := 18090, limit := 18733 } =
      .ok ((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 18221, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_32_t_tail0 :
    instructionSequenceAt 4210 true { bytes := artifactBytes, pos := 18077, limit := 18733 } =
      .ok ((((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18221, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_28_t_0_t_tail18 :
    instructionSequenceAt 4307 false { bytes := artifactBytes, pos := 16767, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16895, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_28_t_0_t_tail0 :
    instructionSequenceAt 4325 false { bytes := artifactBytes, pos := 16736, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false)[28]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16895, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_tail32 :
    instructionSequenceAt 4276 true { bytes := artifactBytes, pos := 17461, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 17705, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_tail28 :
    instructionSequenceAt 4280 true { bytes := artifactBytes, pos := 17292, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 17705, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_25_t_tail0 :
    instructionSequenceAt 4308 true { bytes := artifactBytes, pos := 17239, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[25]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 17705, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_tail32 :
    instructionSequenceAt 4212 true { bytes := artifactBytes, pos := 18075, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false).drop 32, .otherwise), { bytes := artifactBytes, pos := 18319, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
