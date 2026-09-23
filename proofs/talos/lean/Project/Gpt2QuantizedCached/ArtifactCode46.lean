import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_46_33_t_0_t_tail74 :
    instructionSequenceAt 328 false { bytes := artifactBytes, pos := 14552, limit := 14713 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[33]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 14697, limit := 14713 }) := by
  cbv

@[cbv_eval] theorem sequence_46_33_t_0_t_tail21 :
    instructionSequenceAt 381 false { bytes := artifactBytes, pos := 14405, limit := 14713 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[33]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 14697, limit := 14713 }) := by
  cbv

@[cbv_eval] theorem sequence_46_33_t_0_t_tail0 :
    instructionSequenceAt 402 false { bytes := artifactBytes, pos := 14365, limit := 14713 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[33]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14697, limit := 14713 }) := by
  cbv

@[cbv_eval] theorem sequence_46_33_t_tail0 :
    instructionSequenceAt 404 false { bytes := artifactBytes, pos := 14363, limit := 14713 } =
      .ok ((((((Cache.raw.codes[46]!).body)[33]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14698, limit := 14713 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail33 :
    instructionSequenceAt 406 false { bytes := artifactBytes, pos := 14361, limit := 14713 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 33, .end), { bytes := artifactBytes, pos := 14713, limit := 14713 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail0 :
    instructionSequenceAt 439 false { bytes := artifactBytes, pos := 14274, limit := 14713 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14713, limit := 14713 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 14269, limit := 28315 } = .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 14713, limit := 28315 }) := by
  refine code_eq_of_parts (size := 442)
    (payload := { bytes := artifactBytes, pos := 14271, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 14274, limit := 14713 })
    (bodyFinish := { bytes := artifactBytes, pos := 14713, limit := 14713 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_46_tail0
  · rfl

#print axioms code46_decoded

end Project.Gpt2QuantizedCached.Artifact
