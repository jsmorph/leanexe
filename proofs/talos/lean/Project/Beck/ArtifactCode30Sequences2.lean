import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_tail28 :
    instructionSequenceAt 4216 true { bytes := artifactBytes, pos := 17906, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 18319, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_89_t_tail0 :
    instructionSequenceAt 4244 true { bytes := artifactBytes, pos := 17853, limit := 18733 } =
      .ok ((((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false)[89]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 18319, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_24_t_0_t_tail18 :
    instructionSequenceAt 4378 false { bytes := artifactBytes, pos := 15894, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16022, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_24_t_0_t_tail0 :
    instructionSequenceAt 4396 false { bytes := artifactBytes, pos := 15863, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody false)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16022, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_30_t_0_t_tail18 :
    instructionSequenceAt 4372 false { bytes := artifactBytes, pos := 16299, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[30]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 16427, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_30_t_0_t_tail0 :
    instructionSequenceAt 4390 false { bytes := artifactBytes, pos := 16268, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[30]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16427, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_28_t_tail0 :
    instructionSequenceAt 4327 false { bytes := artifactBytes, pos := 16734, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16896, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_65_t_32_t_tail8 :
    instructionSequenceAt 4315 true { bytes := artifactBytes, pos := 16916, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false)[32]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 17047, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
