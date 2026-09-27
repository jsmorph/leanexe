import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode19Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_19_53_t_0_t_tail43 :
    instructionSequenceAt 1461 false { bytes := artifactBytes, pos := 6652, limit := 7717 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false).drop 43, .end), { bytes := artifactBytes, pos := 7661, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_0_t_tail0 :
    instructionSequenceAt 1504 false { bytes := artifactBytes, pos := 6568, limit := 7717 } =
      .ok ((((((((Cache.raw.codes[19]!).body)[53]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7661, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_24_t_tail0 :
    instructionSequenceAt 1535 false { bytes := artifactBytes, pos := 6204, limit := 7717 } =
      .ok ((((((Cache.raw.codes[19]!).body)[24]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6366, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_28_t_tail8 :
    instructionSequenceAt 1523 true { bytes := artifactBytes, pos := 6386, limit := 7717 } =
      .ok ((((((Cache.raw.codes[19]!).body)[28]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 6517, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_28_t_tail0 :
    instructionSequenceAt 1531 true { bytes := artifactBytes, pos := 6373, limit := 7717 } =
      .ok ((((((Cache.raw.codes[19]!).body)[28]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6517, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_53_t_tail0 :
    instructionSequenceAt 1506 false { bytes := artifactBytes, pos := 6566, limit := 7717 } =
      .ok ((((((Cache.raw.codes[19]!).body)[53]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 7662, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_tail53 :
    instructionSequenceAt 1508 false { bytes := artifactBytes, pos := 6564, limit := 7717 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 53, .end), { bytes := artifactBytes, pos := 7717, limit := 7717 }) := by
  cbv

@[cbv_eval] theorem sequence_19_tail28 :
    instructionSequenceAt 1533 false { bytes := artifactBytes, pos := 6371, limit := 7717 } =
      .ok ((((Cache.raw.codes[19]!).body).drop 28, .end), { bytes := artifactBytes, pos := 7717, limit := 7717 }) := by
  cbv


end Project.Beck.Artifact
