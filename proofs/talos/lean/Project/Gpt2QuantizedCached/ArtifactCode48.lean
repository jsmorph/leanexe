import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_48_3_e_14_t_0_t_tail13 :
    instructionSequenceAt 325 false { bytes := artifactBytes, pos := 15170, limit := 15455 } =
      .ok ((((((((((Cache.raw.codes[48]!).body)[3]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 13, .end), { bytes := artifactBytes, pos := 15306, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_14_t_0_t_tail0 :
    instructionSequenceAt 338 false { bytes := artifactBytes, pos := 15142, limit := 15455 } =
      .ok ((((((((((Cache.raw.codes[48]!).body)[3]!).childBody true)[14]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15306, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_14_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 15140, limit := 15455 } =
      .ok ((((((((Cache.raw.codes[48]!).body)[3]!).childBody true)[14]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 15307, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_tail23 :
    instructionSequenceAt 333 false { bytes := artifactBytes, pos := 15323, limit := 15455 } =
      .ok ((((((Cache.raw.codes[48]!).body)[3]!).childBody true).drop 23, .end), { bytes := artifactBytes, pos := 15452, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_tail14 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 15138, limit := 15455 } =
      .ok ((((((Cache.raw.codes[48]!).body)[3]!).childBody true).drop 14, .end), { bytes := artifactBytes, pos := 15452, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_3_e_tail0 :
    instructionSequenceAt 356 false { bytes := artifactBytes, pos := 15110, limit := 15455 } =
      .ok ((((((Cache.raw.codes[48]!).body)[3]!).childBody true).drop 0, .end), { bytes := artifactBytes, pos := 15452, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_tail3 :
    instructionSequenceAt 358 false { bytes := artifactBytes, pos := 15103, limit := 15455 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 3, .end), { bytes := artifactBytes, pos := 15455, limit := 15455 }) := by
  cbv

@[cbv_eval] theorem sequence_48_tail0 :
    instructionSequenceAt 361 false { bytes := artifactBytes, pos := 15094, limit := 15455 } =
      .ok ((((Cache.raw.codes[48]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15455, limit := 15455 }) := by
  cbv

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 15089, limit := 28017 } = .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 15455, limit := 28017 }) := by
  refine code_eq_of_parts (size := 364)
    (payload := { bytes := artifactBytes, pos := 15091, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 15094, limit := 15455 })
    (bodyFinish := { bytes := artifactBytes, pos := 15455, limit := 15455 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_48_tail0
  · rfl

#print axioms code48_decoded

end Project.Gpt2QuantizedCached.Artifact
