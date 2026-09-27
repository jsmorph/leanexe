import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode35Sequences5

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_35_40_e_tail102 :
    instructionSequenceAt 3030 false { bytes := artifactBytes, pos := 24280, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 102, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail98 :
    instructionSequenceAt 3034 false { bytes := artifactBytes, pos := 24111, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 98, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail52 :
    instructionSequenceAt 3080 false { bytes := artifactBytes, pos := 23982, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 52, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail50 :
    instructionSequenceAt 3082 false { bytes := artifactBytes, pos := 23834, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 50, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail46 :
    instructionSequenceAt 3086 false { bytes := artifactBytes, pos := 23665, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 46, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_40_e_tail0 :
    instructionSequenceAt 3132 false { bytes := artifactBytes, pos := 23575, limit := 26239 } =
      .ok ((((((Cache.raw.codes[35]!).body)[40]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 26236, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_tail40 :
    instructionSequenceAt 3134 false { bytes := artifactBytes, pos := 23156, limit := 26239 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 40, .end), { bytes := artifactBytes, pos := 26239, limit := 26239 }) := by
  cbv

@[cbv_eval] theorem sequence_35_tail0 :
    instructionSequenceAt 3174 false { bytes := artifactBytes, pos := 23065, limit := 26239 } =
      .ok ((((Cache.raw.codes[35]!).body).drop 0, .end), { bytes := artifactBytes, pos := 26239, limit := 26239 }) := by
  cbv


end Project.Beck.Artifact
