import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode34Sequences2

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_10_t_tail0 :
    instructionSequenceAt 1293 true { bytes := artifactBytes, pos := 22604, limit := 23060 } =
      .ok ((((((Cache.raw.codes[34]!).body)[10]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 23052, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail10 :
    instructionSequenceAt 1295 false { bytes := artifactBytes, pos := 22602, limit := 23060 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 10, .end), { bytes := artifactBytes, pos := 23060, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail6 :
    instructionSequenceAt 1299 false { bytes := artifactBytes, pos := 21767, limit := 23060 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 6, .end), { bytes := artifactBytes, pos := 23060, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_tail0 :
    instructionSequenceAt 1305 false { bytes := artifactBytes, pos := 21755, limit := 23060 } =
      .ok ((((Cache.raw.codes[34]!).body).drop 0, .end), { bytes := artifactBytes, pos := 23060, limit := 23060 }) := by
  cbv


end Project.Beck.Artifact
