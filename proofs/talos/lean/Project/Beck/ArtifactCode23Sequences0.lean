import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_23_15_t_38_t_0_t_tail18 :
    instructionSequenceAt 519 false { bytes := artifactBytes, pos := 8348, limit := 8808 } =
      .ok ((((((((((Cache.raw.codes[23]!).body)[15]!).childBody false)[38]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 8476, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_38_t_0_t_tail0 :
    instructionSequenceAt 537 false { bytes := artifactBytes, pos := 8317, limit := 8808 } =
      .ok ((((((((((Cache.raw.codes[23]!).body)[15]!).childBody false)[38]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8476, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_38_t_tail0 :
    instructionSequenceAt 539 false { bytes := artifactBytes, pos := 8315, limit := 8808 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[15]!).childBody false)[38]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8477, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_42_t_tail8 :
    instructionSequenceAt 527 true { bytes := artifactBytes, pos := 8497, limit := 8808 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[15]!).childBody false)[42]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 8628, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_42_t_tail0 :
    instructionSequenceAt 535 true { bytes := artifactBytes, pos := 8484, limit := 8808 } =
      .ok ((((((((Cache.raw.codes[23]!).body)[15]!).childBody false)[42]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 8628, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_tail51 :
    instructionSequenceAt 528 true { bytes := artifactBytes, pos := 8642, limit := 8808 } =
      .ok ((((((Cache.raw.codes[23]!).body)[15]!).childBody false).drop 51, .otherwise), { bytes := artifactBytes, pos := 8771, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_tail42 :
    instructionSequenceAt 537 true { bytes := artifactBytes, pos := 8482, limit := 8808 } =
      .ok ((((((Cache.raw.codes[23]!).body)[15]!).childBody false).drop 42, .otherwise), { bytes := artifactBytes, pos := 8771, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_15_t_tail38 :
    instructionSequenceAt 541 true { bytes := artifactBytes, pos := 8313, limit := 8808 } =
      .ok ((((((Cache.raw.codes[23]!).body)[15]!).childBody false).drop 38, .otherwise), { bytes := artifactBytes, pos := 8771, limit := 8808 }) := by
  cbv


end Project.Beck.Artifact
