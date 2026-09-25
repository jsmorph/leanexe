import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_22_tail15 :
    instructionSequenceAt 558 false { bytes := artifactBytes, pos := 2662, limit := 2808 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 15, .end), { bytes := artifactBytes, pos := 2808, limit := 2808 }) := by
  cbv

@[cbv_eval] theorem sequence_22_tail13 :
    instructionSequenceAt 560 false { bytes := artifactBytes, pos := 2527, limit := 2808 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 13, .end), { bytes := artifactBytes, pos := 2808, limit := 2808 }) := by
  cbv

@[cbv_eval] theorem sequence_22_tail11 :
    instructionSequenceAt 562 false { bytes := artifactBytes, pos := 2395, limit := 2808 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 11, .end), { bytes := artifactBytes, pos := 2808, limit := 2808 }) := by
  cbv

@[cbv_eval] theorem sequence_22_tail9 :
    instructionSequenceAt 564 false { bytes := artifactBytes, pos := 2256, limit := 2808 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 9, .end), { bytes := artifactBytes, pos := 2808, limit := 2808 }) := by
  cbv

@[cbv_eval] theorem sequence_22_tail0 :
    instructionSequenceAt 573 false { bytes := artifactBytes, pos := 2235, limit := 2808 } =
      .ok ((((Cache.raw.codes[22]!).body).drop 0, .end), { bytes := artifactBytes, pos := 2808, limit := 2808 }) := by
  cbv

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2230, limit := 28017 } = .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 2808, limit := 28017 }) := by
  refine code_eq_of_parts (size := 576)
    (payload := { bytes := artifactBytes, pos := 2232, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 2235, limit := 2808 })
    (bodyFinish := { bytes := artifactBytes, pos := 2808, limit := 2808 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_22_tail0
  · rfl

#print axioms code22_decoded

end Project.Gpt2QuantizedCached.Artifact
