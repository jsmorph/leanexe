import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_53_36_t_0_t_tail18 :
    instructionSequenceAt 471 false { bytes := artifactBytes, pos := 20441, limit := 20833 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[36]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 20569, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_36_t_0_t_tail0 :
    instructionSequenceAt 489 false { bytes := artifactBytes, pos := 20410, limit := 20833 } =
      .ok ((((((((Cache.raw.codes[53]!).body)[36]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20569, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_36_t_tail0 :
    instructionSequenceAt 491 false { bytes := artifactBytes, pos := 20408, limit := 20833 } =
      .ok ((((((Cache.raw.codes[53]!).body)[36]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20570, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_40_t_tail8 :
    instructionSequenceAt 479 true { bytes := artifactBytes, pos := 20590, limit := 20833 } =
      .ok ((((((Cache.raw.codes[53]!).body)[40]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 20721, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_40_t_tail0 :
    instructionSequenceAt 487 true { bytes := artifactBytes, pos := 20577, limit := 20833 } =
      .ok ((((((Cache.raw.codes[53]!).body)[40]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 20721, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_tail40 :
    instructionSequenceAt 489 false { bytes := artifactBytes, pos := 20575, limit := 20833 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 40, .end), { bytes := artifactBytes, pos := 20833, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_tail36 :
    instructionSequenceAt 493 false { bytes := artifactBytes, pos := 20406, limit := 20833 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 36, .end), { bytes := artifactBytes, pos := 20833, limit := 20833 }) := by
  cbv

@[cbv_eval] theorem sequence_53_tail0 :
    instructionSequenceAt 529 false { bytes := artifactBytes, pos := 20304, limit := 20833 } =
      .ok ((((Cache.raw.codes[53]!).body).drop 0, .end), { bytes := artifactBytes, pos := 20833, limit := 20833 }) := by
  cbv

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 20299, limit := 28315 } = .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 20833, limit := 28315 }) := by
  refine code_eq_of_parts (size := 532)
    (payload := { bytes := artifactBytes, pos := 20301, limit := 28315 })
    (bodyStart := { bytes := artifactBytes, pos := 20304, limit := 20833 })
    (bodyFinish := { bytes := artifactBytes, pos := 20833, limit := 20833 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_53_tail0
  · rfl

#print axioms code53_decoded

end Project.Gpt2QuantizedCached.Artifact
