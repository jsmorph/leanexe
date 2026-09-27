import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode34Sequences0

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_e_tail31 :
    instructionSequenceAt 1188 false { bytes := artifactBytes, pos := 22454, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody true).drop 31, .end), { bytes := artifactBytes, pos := 22592, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_47_e_tail0 :
    instructionSequenceAt 1219 false { bytes := artifactBytes, pos := 22350, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true)[47]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 22592, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_26_t_0_t_tail18 :
    instructionSequenceAt 1225 false { bytes := artifactBytes, pos := 22743, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true)[26]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 22871, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_26_t_0_t_tail0 :
    instructionSequenceAt 1243 false { bytes := artifactBytes, pos := 22712, limit := 23060 } =
      .ok ((((((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true)[26]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22871, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_tail47 :
    instructionSequenceAt 1221 false { bytes := artifactBytes, pos := 21951, limit := 23060 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true).drop 47, .end), { bytes := artifactBytes, pos := 22593, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_25_e_tail0 :
    instructionSequenceAt 1268 false { bytes := artifactBytes, pos := 21849, limit := 23060 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false)[25]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 22593, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_26_t_tail0 :
    instructionSequenceAt 1245 false { bytes := artifactBytes, pos := 22710, limit := 23060 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true)[26]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22872, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_30_t_tail8 :
    instructionSequenceAt 1233 true { bytes := artifactBytes, pos := 22892, limit := 23060 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true)[30]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 23023, limit := 23060 }) := by
  cbv


end Project.Beck.Artifact
