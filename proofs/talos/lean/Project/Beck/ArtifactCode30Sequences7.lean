import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences6

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_156_t_tail0 :
    instructionSequenceAt 4556 true { bytes := artifactBytes, pos := 15096, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[156]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15240, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_195_t_tail0 :
    instructionSequenceAt 4517 false { bytes := artifactBytes, pos := 15315, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[195]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15477, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_199_t_tail8 :
    instructionSequenceAt 4505 true { bytes := artifactBytes, pos := 15497, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[199]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 15628, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_199_t_tail0 :
    instructionSequenceAt 4513 true { bytes := artifactBytes, pos := 15484, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[199]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15628, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_tail28 :
    instructionSequenceAt 4396 true { bytes := artifactBytes, pos := 16028, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody false).drop 28, .otherwise), { bytes := artifactBytes, pos := 16206, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_tail24 :
    instructionSequenceAt 4400 true { bytes := artifactBytes, pos := 15859, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody false).drop 24, .otherwise), { bytes := artifactBytes, pos := 16206, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_t_tail0 :
    instructionSequenceAt 4424 true { bytes := artifactBytes, pos := 15813, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 16206, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_tail85 :
    instructionSequenceAt 4339 false { bytes := artifactBytes, pos := 17185, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody true).drop 85, .end), { bytes := artifactBytes, pos := 18526, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
