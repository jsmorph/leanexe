import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Beck.ArtifactCode30Sequences7

namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_30_288_e_tail65 :
    instructionSequenceAt 4359 false { bytes := artifactBytes, pos := 16677, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody true).drop 65, .end), { bytes := artifactBytes, pos := 18526, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_tail34 :
    instructionSequenceAt 4390 false { bytes := artifactBytes, pos := 16433, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody true).drop 34, .end), { bytes := artifactBytes, pos := 18526, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_tail30 :
    instructionSequenceAt 4394 false { bytes := artifactBytes, pos := 16264, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody true).drop 30, .end), { bytes := artifactBytes, pos := 18526, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_288_e_tail0 :
    instructionSequenceAt 4424 false { bytes := artifactBytes, pos := 16206, limit := 18733 } =
      .ok ((((((Cache.raw.codes[30]!).body)[288]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 18526, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail306 :
    instructionSequenceAt 4408 false { bytes := artifactBytes, pos := 18596, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 306, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail288 :
    instructionSequenceAt 4426 false { bytes := artifactBytes, pos := 15811, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 288, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail228 :
    instructionSequenceAt 4486 false { bytes := artifactBytes, pos := 15683, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 228, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv

@[cbv_eval] theorem sequence_30_tail199 :
    instructionSequenceAt 4515 false { bytes := artifactBytes, pos := 15482, limit := 18733 } =
      .ok ((((Cache.raw.codes[30]!).body).drop 199, .end), { bytes := artifactBytes, pos := 18733, limit := 18733 }) := by
  cbv


end Project.Beck.Artifact
