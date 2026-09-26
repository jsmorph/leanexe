import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_62_18_t_0_t_tail18 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 27265, limit := 27555 } =
      .ok ((((((((Cache.raw.codes[62]!).body)[18]!).childBody false)[0]!).childBody false).drop 18, .end), { bytes := artifactBytes, pos := 27393, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_18_t_0_t_tail0 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 27234, limit := 27555 } =
      .ok ((((((((Cache.raw.codes[62]!).body)[18]!).childBody false)[0]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27393, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_18_t_tail0 :
    instructionSequenceAt 342 false { bytes := artifactBytes, pos := 27232, limit := 27555 } =
      .ok ((((((Cache.raw.codes[62]!).body)[18]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27394, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_22_t_tail8 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 27414, limit := 27555 } =
      .ok ((((((Cache.raw.codes[62]!).body)[22]!).childBody false).drop 8, .end), { bytes := artifactBytes, pos := 27545, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_22_t_tail0 :
    instructionSequenceAt 338 true { bytes := artifactBytes, pos := 27401, limit := 27555 } =
      .ok ((((((Cache.raw.codes[62]!).body)[22]!).childBody false).drop 0, .end), { bytes := artifactBytes, pos := 27545, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_tail22 :
    instructionSequenceAt 340 false { bytes := artifactBytes, pos := 27399, limit := 27555 } =
      .ok ((((Cache.raw.codes[62]!).body).drop 22, .end), { bytes := artifactBytes, pos := 27555, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_tail18 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 27230, limit := 27555 } =
      .ok ((((Cache.raw.codes[62]!).body).drop 18, .end), { bytes := artifactBytes, pos := 27555, limit := 27555 }) := by
  cbv

@[cbv_eval] theorem sequence_62_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 27193, limit := 27555 } =
      .ok ((((Cache.raw.codes[62]!).body).drop 0, .end), { bytes := artifactBytes, pos := 27555, limit := 27555 }) := by
  cbv

theorem code62_decoded :
    code { bytes := artifactBytes, pos := 27188, limit := 28017 } = .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 27555, limit := 28017 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 27190, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 27193, limit := 27555 })
    (bodyFinish := { bytes := artifactBytes, pos := 27555, limit := 27555 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_62_tail0
  · rfl

#print axioms code62_decoded

end Project.Gpt2QuantizedCached.Artifact
