import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences5

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_66_t_tail0 :
    instructionSequenceAt 4646 false { bytes := artifactBytes, pos := 14151, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[66]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14313, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_tail8 :
    instructionSequenceAt 4634 true { bytes := artifactBytes, pos := 14333, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[70]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 14464, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_70_t_tail0 :
    instructionSequenceAt 4642 true { bytes := artifactBytes, pos := 14320, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[70]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14464, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_109_t_tail0 :
    instructionSequenceAt 4603 false { bytes := artifactBytes, pos := 14539, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[109]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14701, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_113_t_tail8 :
    instructionSequenceAt 4591 true { bytes := artifactBytes, pos := 14721, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[113]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 14852, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_113_t_tail0 :
    instructionSequenceAt 4599 true { bytes := artifactBytes, pos := 14708, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[113]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14852, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_152_t_tail0 :
    instructionSequenceAt 4560 false { bytes := artifactBytes, pos := 14927, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[152]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15089, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_156_t_tail8 :
    instructionSequenceAt 4548 true { bytes := artifactBytes, pos := 15109, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[156]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 15240, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
