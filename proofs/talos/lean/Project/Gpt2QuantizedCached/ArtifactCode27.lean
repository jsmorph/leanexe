import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_27_tail29 :
    instructionSequenceAt 992 false { bytes := artifactBytes, pos := 4471, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 29, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail27 :
    instructionSequenceAt 994 false { bytes := artifactBytes, pos := 4303, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 27, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail25 :
    instructionSequenceAt 996 false { bytes := artifactBytes, pos := 4135, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 25, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail23 :
    instructionSequenceAt 998 false { bytes := artifactBytes, pos := 3968, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 23, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail21 :
    instructionSequenceAt 1000 false { bytes := artifactBytes, pos := 3800, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 21, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail19 :
    instructionSequenceAt 1002 false { bytes := artifactBytes, pos := 3632, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 19, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

@[cbv_eval] theorem sequence_27_tail0 :
    instructionSequenceAt 1021 false { bytes := artifactBytes, pos := 3595, limit := 4616 } =
      .ok ((((Cache.raw.codes[27]!).body).drop 0, .end), { bytes := artifactBytes, pos := 4616, limit := 4616 }) := by
  cbv

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 3590, limit := 28315 } = .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 4616, limit := 28315 }) := by
  refine code_eq_of_parts (size := 1024)
    (payload := { bytes := artifactBytes, pos := 3592, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 3595, limit := 4616 })
    (bodyFinish := { bytes := artifactBytes, pos := 4616, limit := 4616 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_27_tail0
  · rfl

#print axioms code27_decoded

end Project.Gpt2QuantizedCached.Artifact
