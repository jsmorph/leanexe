import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_38_10_t_0_t_tail36 :
    instructionSequenceAt 202 false { bytes := artifactBytes, pos := 10939, limit := 11084 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[10]!).childBody false)[0]!).childBody false).drop 36, .end), { bytes := artifactBytes, pos := 11068, limit := 11084 }) := by
  cbv

@[cbv_eval] theorem sequence_38_10_t_0_t_tail0 :
    instructionSequenceAt 238 false { bytes := artifactBytes, pos := 10856, limit := 11084 } =
      .ok ((((((((Cache.raw.codes[38]!).body)[10]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11068, limit := 11084 }) := by
  cbv

@[cbv_eval] theorem sequence_38_10_t_tail0 :
    instructionSequenceAt 240 false { bytes := artifactBytes, pos := 10854, limit := 11084 } =
      .ok ((((((Cache.raw.codes[38]!).body)[10]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 11069, limit := 11084 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail10 :
    instructionSequenceAt 242 false { bytes := artifactBytes, pos := 10852, limit := 11084 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 10, .end), { bytes := artifactBytes, pos := 11084, limit := 11084 }) := by
  cbv

@[cbv_eval] theorem sequence_38_tail0 :
    instructionSequenceAt 252 false { bytes := artifactBytes, pos := 10832, limit := 11084 } =
      .ok ((((Cache.raw.codes[38]!).body).drop 0, .end), { bytes := artifactBytes, pos := 11084, limit := 11084 }) := by
  cbv

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 10827, limit := 28017 } = .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 11084, limit := 28017 }) := by
  refine code_eq_of_parts (size := 255)
    (payload := { bytes := artifactBytes, pos := 10829, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 10832, limit := 11084 })
    (bodyFinish := { bytes := artifactBytes, pos := 11084, limit := 11084 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_38_tail0
  · rfl

#print axioms code38_decoded

end Project.Gpt2QuantizedCached.Artifact
