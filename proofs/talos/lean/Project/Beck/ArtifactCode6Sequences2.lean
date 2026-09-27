import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode6Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_6_7_e_20_e_tail0 :
    instructionSequenceAt 1292 false { bytes := artifactBytes, pos := 3905, limit := 5006 } =
      .ok ((((((((Cache.raw.codes[6]!).body)[7]!).childBody true)[20]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 4992, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_tail20 :
    instructionSequenceAt 1294 false { bytes := artifactBytes, pos := 3858, limit := 5006 } =
      .ok ((((((Cache.raw.codes[6]!).body)[7]!).childBody true).drop 20, .end), { bytes := artifactBytes, pos := 4993, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_7_e_tail0 :
    instructionSequenceAt 1314 false { bytes := artifactBytes, pos := 3743, limit := 5006 } =
      .ok ((((((Cache.raw.codes[6]!).body)[7]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 4993, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail7 :
    instructionSequenceAt 1316 false { bytes := artifactBytes, pos := 3696, limit := 5006 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 7, .end), { bytes := artifactBytes, pos := 5006, limit := 5006 }) := by
  cbv

@[cbv_eval] theorem sequence_6_tail0 :
    instructionSequenceAt 1323 false { bytes := artifactBytes, pos := 3683, limit := 5006 } =
      .ok ((((Cache.raw.codes[6]!).body).drop 0, .end), { bytes := artifactBytes, pos := 5006, limit := 5006 }) := by
  cbv


end Project.Beck.Artifact
