import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences3

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_109_t_0_t_tail18 :
    instructionSequenceAt 4583 false { bytes := artifactBytes, pos := 14572, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[109]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 14700, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_109_t_0_t_tail0 :
    instructionSequenceAt 4601 false { bytes := artifactBytes, pos := 14541, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[109]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14700, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_152_t_0_t_tail18 :
    instructionSequenceAt 4540 false { bytes := artifactBytes, pos := 14960, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[152]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 15088, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_152_t_0_t_tail0 :
    instructionSequenceAt 4558 false { bytes := artifactBytes, pos := 14929, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[152]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15088, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_195_t_0_t_tail18 :
    instructionSequenceAt 4497 false { bytes := artifactBytes, pos := 15348, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[195]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 15476, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_195_t_0_t_tail0 :
    instructionSequenceAt 4515 false { bytes := artifactBytes, pos := 15317, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[195]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15476, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_24_t_tail0 :
    instructionSequenceAt 4398 false { bytes := artifactBytes, pos := 15861, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody false)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 16023, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_28_t_tail8 :
    instructionSequenceAt 4386 true { bytes := artifactBytes, pos := 16043, limit := 18733 } =
      .ok ((((((((Cache.raw.codes[30]!).body)[288]!).childBody false)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 16174, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
