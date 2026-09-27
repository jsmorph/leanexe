import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_46_31_t_0_t_tail74 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 14452, limit := 14609 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[31]!).childBody false)[0]!).childBody false).drop 74, .end), { bytes := artifactBytes, pos := 14593, limit := 14609 }) := by
  cbv

@[cbv_eval] theorem sequence_46_31_t_0_t_tail21 :
    instructionSequenceAt 375 false { bytes := artifactBytes, pos := 14305, limit := 14609 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[31]!).childBody false)[0]!).childBody false).drop 21, .end), { bytes := artifactBytes, pos := 14593, limit := 14609 }) := by
  cbv

@[cbv_eval] theorem sequence_46_31_t_0_t_tail0 :
    instructionSequenceAt 396 false { bytes := artifactBytes, pos := 14265, limit := 14609 } =
      .ok ((((((((Cache.raw.codes[46]!).body)[31]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14593, limit := 14609 }) := by
  cbv

@[cbv_eval] theorem sequence_46_31_t_tail0 :
    instructionSequenceAt 398 false { bytes := artifactBytes, pos := 14263, limit := 14609 } =
      .ok ((((((Cache.raw.codes[46]!).body)[31]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 14594, limit := 14609 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail31 :
    instructionSequenceAt 400 false { bytes := artifactBytes, pos := 14261, limit := 14609 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 31, .end), { bytes := artifactBytes, pos := 14609, limit := 14609 }) := by
  cbv

@[cbv_eval] theorem sequence_46_tail0 :
    instructionSequenceAt 431 false { bytes := artifactBytes, pos := 14178, limit := 14609 } =
      .ok ((((Cache.raw.codes[46]!).body).drop 0, .end), { bytes := artifactBytes, pos := 14609, limit := 14609 }) := by
  cbv

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 14173, limit := 28017 } = .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 14609, limit := 28017 }) := by
  refine code_eq_of_parts (size := 434)
    (payload := { bytes := artifactBytes, pos := 14175, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 14178, limit := 14609 })
    (bodyFinish := { bytes := artifactBytes, pos := 14609, limit := 14609 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_46_tail0
  · rfl

#print axioms code46_decoded

end Project.Gpt2QuantizedCached.Artifact
