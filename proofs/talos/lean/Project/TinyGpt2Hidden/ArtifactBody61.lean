import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence61_tail8 :
    instructionSequenceAt 17 false { bytes := artifactBytes, pos := 7839, limit := 7840 } =
      .ok (((Cache.raw.codes[61]!.body).drop 8, .end), { bytes := artifactBytes, pos := 7840, limit := 7840 }) := by cbv

@[cbv_eval] theorem sequence61_tail0 :
    instructionSequenceAt 25 false { bytes := artifactBytes, pos := 7815, limit := 7840 } =
      .ok (((Cache.raw.codes[61]!.body).drop 0, .end), { bytes := artifactBytes, pos := 7840, limit := 7840 }) := by cbv

theorem code61_decoded_parts :
    code { bytes := artifactBytes, pos := 7811, limit := 16006 } = .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 7840, limit := 16006 }) := by
  refine code_eq_of_parts (size := 28)
    (payload := { bytes := artifactBytes, pos := 7812, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 7815, limit := 7840 })
    (bodyFinish := { bytes := artifactBytes, pos := 7840, limit := 7840 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence61_tail0
  · rfl

#print axioms code61_decoded_parts
end Project.TinyGpt2Hidden.Artifact
