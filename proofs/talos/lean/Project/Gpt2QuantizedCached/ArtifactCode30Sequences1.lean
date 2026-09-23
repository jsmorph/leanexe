import Project.Gpt2QuantizedCached.ArtifactCode30Sequences0
import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_70_t_tail0 :
    instructionSequenceAt 804 false { bytes := artifactBytes, pos := 6173, limit := 6531 } =
      .ok ((((((Cache.raw.codes[30]!).body)[70]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 6508, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail70 :
    instructionSequenceAt 806 false { bytes := artifactBytes, pos := 6171, limit := 6531 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 70, .end), { bytes := artifactBytes, pos := 6531, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail61 :
    instructionSequenceAt 815 false { bytes := artifactBytes, pos := 6010, limit := 6531 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 61, .end), { bytes := artifactBytes, pos := 6531, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail57 :
    instructionSequenceAt 819 false { bytes := artifactBytes, pos := 5841, limit := 6531 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 57, .end), { bytes := artifactBytes, pos := 6531, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail19 :
    instructionSequenceAt 857 false { bytes := artifactBytes, pos := 5713, limit := 6531 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 19, .end), { bytes := artifactBytes, pos := 6531, limit := 6531 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail0 :
    instructionSequenceAt 876 false { bytes := artifactBytes, pos := 5655, limit := 6531 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 0, .end), { bytes := artifactBytes, pos := 6531, limit := 6531 }) := by
  cbv


end Project.Gpt2QuantizedCached.Artifact
