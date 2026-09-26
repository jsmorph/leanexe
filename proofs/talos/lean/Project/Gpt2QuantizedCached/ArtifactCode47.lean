import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

@[cbv_eval] theorem sequence_47_tail237 :
    instructionSequenceAt 238 false { bytes := artifactBytes, pos := 14960, limit := 15089 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 237, .end), { bytes := artifactBytes, pos := 15089, limit := 15089 }) := by
  cbv

@[cbv_eval] theorem sequence_47_tail148 :
    instructionSequenceAt 327 false { bytes := artifactBytes, pos := 14832, limit := 15089 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 148, .end), { bytes := artifactBytes, pos := 15089, limit := 15089 }) := by
  cbv

@[cbv_eval] theorem sequence_47_tail60 :
    instructionSequenceAt 415 false { bytes := artifactBytes, pos := 14704, limit := 15089 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 60, .end), { bytes := artifactBytes, pos := 15089, limit := 15089 }) := by
  cbv

@[cbv_eval] theorem sequence_47_tail0 :
    instructionSequenceAt 475 false { bytes := artifactBytes, pos := 14614, limit := 15089 } =
      .ok ((((Cache.raw.codes[47]!).body).drop 0, .end), { bytes := artifactBytes, pos := 15089, limit := 15089 }) := by
  cbv

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 14609, limit := 28017 } = .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 15089, limit := 28017 }) := by
  refine code_eq_of_parts (size := 478)
    (payload := { bytes := artifactBytes, pos := 14611, limit := 28017 })
    (bodyStart := { bytes := artifactBytes, pos := 14614, limit := 15089 })
    (bodyFinish := { bytes := artifactBytes, pos := 15089, limit := 15089 })
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence_47_tail0
  · rfl

#print axioms code47_decoded

end Project.Gpt2QuantizedCached.Artifact
