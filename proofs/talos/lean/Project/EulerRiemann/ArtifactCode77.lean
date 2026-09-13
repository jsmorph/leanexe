import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem code77_seq_77_47_t_0_t_tail93_decoded :
    instructionSequenceAt 687 false { bytes := artifactBytes, pos := 9782, limit := 10056 } =
      .ok ((((((((Cache.raw.codes[77]!).body)[47]!).childBody false)[0]!).childBody false).drop 93, .end), { bytes := artifactBytes, pos := 10038, limit := 10056 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_47_t_0_t_tail0_decoded :
    instructionSequenceAt 780 false { bytes := artifactBytes, pos := 9625, limit := 10056 } =
      .ok ((((((((Cache.raw.codes[77]!).body)[47]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10038, limit := 10056 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_47_t_tail0_decoded :
    instructionSequenceAt 782 false { bytes := artifactBytes, pos := 9623, limit := 10056 } =
      .ok ((((((Cache.raw.codes[77]!).body)[47]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 10039, limit := 10056 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_tail47_decoded :
    instructionSequenceAt 784 false { bytes := artifactBytes, pos := 9621, limit := 10056 } =
      .ok ((((Cache.raw.codes[77]!).body).drop 47, .end), { bytes := artifactBytes, pos := 10056, limit := 10056 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_tail30_decoded :
    instructionSequenceAt 801 false { bytes := artifactBytes, pos := 9283, limit := 10056 } =
      .ok ((((Cache.raw.codes[77]!).body).drop 30, .end), { bytes := artifactBytes, pos := 10056, limit := 10056 }) := by
  cbv

@[cbv_eval] theorem code77_seq_77_tail0_decoded :
    instructionSequenceAt 831 false { bytes := artifactBytes, pos := 9225, limit := 10056 } =
      .ok ((((Cache.raw.codes[77]!).body).drop 0, .end), { bytes := artifactBytes, pos := 10056, limit := 10056 }) := by
  cbv

theorem code77_decoded :
    code { bytes := artifactBytes, pos := 9220, limit := 21767 } =
      .ok (Cache.raw.codes[77]!, { bytes := artifactBytes, pos := 10056, limit := 21767 }) := by
  refine code_eq_of_parts (size := 834)
    (payload := { bytes := artifactBytes, pos := 9222, limit := 21767 })
    (bodyStart := { bytes := artifactBytes, pos := 9225, limit := 10056 })
    (bodyFinish := { bytes := artifactBytes, pos := 10056, limit := 10056 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact code77_seq_77_tail0_decoded
  · rfl

#print axioms code77_decoded

end Project.EulerRiemann.Artifact
