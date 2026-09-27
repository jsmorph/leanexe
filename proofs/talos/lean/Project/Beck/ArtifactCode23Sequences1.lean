import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode23Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_23_15_t_tail0 :
    instructionSequenceAt 579 true { bytes := artifactBytes, pos := 8243, limit := 8808 } =
      .ok ((((((Cache.raw.codes[23]!).body)[15]!).childBody false).drop 0, .otherwise), { bytes := artifactBytes, pos := 8771, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail15 :
    instructionSequenceAt 581 false { bytes := artifactBytes, pos := 8241, limit := 8808 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 15, .end), { bytes := artifactBytes, pos := 8808, limit := 8808 }) := by
  cbv

@[cbv_eval] theorem sequence_23_tail0 :
    instructionSequenceAt 596 false { bytes := artifactBytes, pos := 8212, limit := 8808 } =
      .ok ((((Cache.raw.codes[23]!).body).drop 0, .end), { bytes := artifactBytes, pos := 8808, limit := 8808 }) := by
  cbv


end Project.Beck.Artifact
