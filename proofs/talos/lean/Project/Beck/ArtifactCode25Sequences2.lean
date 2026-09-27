import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode25Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_25_21_e_tail42 :
    instructionSequenceAt 1223 false { bytes := artifactBytes, pos := 9811, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 42, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_21_e_tail0 :
    instructionSequenceAt 1265 false { bytes := artifactBytes, pos := 9731, limit := 10915 } =
      .ok ((((((Cache.raw.codes[25]!).body)[21]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 10902, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_tail21 :
    instructionSequenceAt 1267 false { bytes := artifactBytes, pos := 9704, limit := 10915 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 21, .end), { bytes := artifactBytes, pos := 10915, limit := 10915 }) := by
  cbv

@[cbv_eval] theorem sequence_25_tail0 :
    instructionSequenceAt 1288 false { bytes := artifactBytes, pos := 9627, limit := 10915 } =
      .ok ((((Cache.raw.codes[25]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10915, limit := 10915 }) := by
  cbv


end Project.Beck.Artifact
