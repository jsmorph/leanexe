import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode34Sequences1

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_34_10_t_18_e_30_t_tail0 :
    instructionSequenceAt 1241 true { bytes := artifactBytes, pos := 22879, limit := 23060 } =
      .ok ((((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true)[30]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 23023, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_tail25 :
    instructionSequenceAt 1270 false { bytes := artifactBytes, pos := 21830, limit := 23060 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false).drop 25, .end), { bytes := artifactBytes, pos := 22596, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_0_t_tail0 :
    instructionSequenceAt 1295 false { bytes := artifactBytes, pos := 21771, limit := 23060 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[6]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22596, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_tail30 :
    instructionSequenceAt 1243 false { bytes := artifactBytes, pos := 22877, limit := 23060 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true).drop 30, .end), { bytes := artifactBytes, pos := 23051, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_tail26 :
    instructionSequenceAt 1247 false { bytes := artifactBytes, pos := 22708, limit := 23060 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true).drop 26, .end), { bytes := artifactBytes, pos := 23051, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_18_e_tail0 :
    instructionSequenceAt 1273 false { bytes := artifactBytes, pos := 22658, limit := 23060 } =
      .ok ((((((((Cache.raw.codes[34]!).body)[10]!).childBody false)[18]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 23051, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_6_t_tail0 :
    instructionSequenceAt 1297 false { bytes := artifactBytes, pos := 21769, limit := 23060 } =
      .ok ((((((Cache.raw.codes[34]!).body)[6]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 22597, limit := 23060 }) := by
  cbv

@[cbv_eval] theorem sequence_34_10_t_tail18 :
    instructionSequenceAt 1275 true { bytes := artifactBytes, pos := 22643, limit := 23060 } =
      .ok ((((((Cache.raw.codes[34]!).body)[10]!).childBody false).drop 18, .otherwise), { bytes := artifactBytes, pos := 23052, limit := 23060 }) := by
  cbv


end Project.Beck.Artifact
