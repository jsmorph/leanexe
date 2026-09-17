import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence10_tail47 :
    instructionSequenceAt 33 false { bytes := artifactBytes, pos := 2305, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 47, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

@[cbv_eval] theorem sequence10_tail40 :
    instructionSequenceAt 40 false { bytes := artifactBytes, pos := 2296, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 40, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

@[cbv_eval] theorem sequence10_tail32 :
    instructionSequenceAt 48 false { bytes := artifactBytes, pos := 2274, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 32, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

@[cbv_eval] theorem sequence10_tail24 :
    instructionSequenceAt 56 false { bytes := artifactBytes, pos := 2261, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 24, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

@[cbv_eval] theorem sequence10_tail16 :
    instructionSequenceAt 64 false { bytes := artifactBytes, pos := 2249, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 16, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

@[cbv_eval] theorem sequence10_tail8 :
    instructionSequenceAt 72 false { bytes := artifactBytes, pos := 2238, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

@[cbv_eval] theorem sequence10_tail0 :
    instructionSequenceAt 80 false { bytes := artifactBytes, pos := 2226, limit := 2306 } =
      .ok (((Cache.raw.codes[10]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2306, limit := 2306 }) := by cbv

theorem code10_decoded_parts :
    code { bytes := artifactBytes, pos := 2222, limit := 16006 } = .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 2306, limit := 16006 }) := by
  refine code_eq_of_parts (size := 83)
    (payload := { bytes := artifactBytes, pos := 2223, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 2226, limit := 2306 })
    (bodyFinish := { bytes := artifactBytes, pos := 2306, limit := 2306 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence10_tail0
  · rfl

#print axioms code10_decoded_parts
end Project.TinyGpt2Hidden.Artifact
