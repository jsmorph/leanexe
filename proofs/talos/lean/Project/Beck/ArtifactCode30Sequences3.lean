import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_288_e_65_t_32_t_tail0 :
    instructionSequenceAt 4323 true { bytes := artifactBytes, pos := 16903, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[65]!).childBody false)[32]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 17047, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_tail103 :
    instructionSequenceAt 4232 false { bytes := artifactBytes, pos := 18345, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false).drop 103, .end), { bytes := artifactBytes, pos := 18474, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_tail89 :
    instructionSequenceAt 4246 false { bytes := artifactBytes, pos := 17851, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false).drop 89, .end), { bytes := artifactBytes, pos := 18474, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_tail34 :
    instructionSequenceAt 4301 false { bytes := artifactBytes, pos := 17723, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false).drop 34, .end), { bytes := artifactBytes, pos := 18474, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_tail25 :
    instructionSequenceAt 4310 false { bytes := artifactBytes, pos := 17237, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false).drop 25, .end), { bytes := artifactBytes, pos := 18474, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_85_t_0_t_tail0 :
    instructionSequenceAt 4335 false { bytes := artifactBytes, pos := 17189, limit := 18733 } =
      .ok ((((((((((Cache.raw.codes[30]!).body)[288]!).childBody true)[85]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 18474, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_66_t_0_t_tail18 :
    instructionSequenceAt 4626 false { bytes := artifactBytes, pos := 14184, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[66]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 14312, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_66_t_0_t_tail0 :
    instructionSequenceAt 4644 false { bytes := artifactBytes, pos := 14153, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[66]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14312, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
