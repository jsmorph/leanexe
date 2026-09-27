import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode19Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_tail36 :
    instructionSequenceAt 1407 false { bytes := artifactBytes, pos := 6759, limit := 7717 } =
      .ok ((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 36, .end), { bytes := artifactBytes, pos := 7440, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_0_t_tail0 :
    instructionSequenceAt 1443 false { bytes := artifactBytes, pos := 6682, limit := 7717 } =
      .ok ((((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7440, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_12_t_tail0 :
    instructionSequenceAt 1445 false { bytes := artifactBytes, pos := 6680, limit := 7717 } =
      .ok ((((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false)[12]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7441, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_tail12 :
    instructionSequenceAt 1447 true { bytes := artifactBytes, pos := 6678, limit := 7717 } =
      .ok ((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false).drop 12, .otherwise), { bytes := artifactBytes, pos := 7520, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_43_t_tail0 :
    instructionSequenceAt 1459 true { bytes := artifactBytes, pos := 6654, limit := 7717 } =
      .ok ((((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false)[43]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 7520, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_24_t_0_t_tail18 :
    instructionSequenceAt 1515 false { bytes := artifactBytes, pos := 6237, limit := 7717 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[24]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 6365, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_24_t_0_t_tail0 :
    instructionSequenceAt 1533 false { bytes := artifactBytes, pos := 6206, limit := 7717 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[24]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6365, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_tail46 :
    instructionSequenceAt 1458 false { bytes := artifactBytes, pos := 7533, limit := 7717 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false).drop 46, .end), { bytes := artifactBytes, pos := 7661, limit := 7717 }) := by
  cbv


end Project.Beck.Artifact
