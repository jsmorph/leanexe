import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.ByteIO.ArtifactCode0
import Project.ByteIO.ArtifactCode1
import Project.ByteIO.ArtifactCode2
import Project.ByteIO.ArtifactCode3
import Project.ByteIO.ArtifactCode4
import Project.ByteIO.ArtifactCode5

namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes ByteLookup.data
attribute [local cbv_eval] ByteLookup.bytes_data ByteLookup.bytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail6 :
    Internal.vectorLoop code 0 { bytes := bytes, pos := 2082, limit := 2082 } =
      .ok (raw.core.codes.drop 6, { bytes := bytes, pos := 2082, limit := 2082 }) := by rfl

theorem codes_tail5 :
    Internal.vectorLoop code 1 { bytes := bytes, pos := 1781, limit := 2082 } =
      .ok (raw.core.codes.drop 5, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 2 { bytes := bytes, pos := 1428, limit := 2082 } =
      .ok (raw.core.codes.drop 4, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 3 { bytes := bytes, pos := 1419, limit := 2082 } =
      .ok (raw.core.codes.drop 3, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 4 { bytes := bytes, pos := 1161, limit := 2082 } =
      .ok (raw.core.codes.drop 2, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 5 { bytes := bytes, pos := 490, limit := 2082 } =
      .ok (raw.core.codes.drop 1, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 6 { bytes := bytes, pos := 372, limit := 2082 } =
      .ok (raw.core.codes.drop 0, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := bytes, pos := 371, limit := 2082 } =
      .ok (raw.core.codes, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  refine vector_eq_of_parts (length := 6)
    (itemsStart := { bytes := bytes, pos := 372, limit := 2082 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := bytes, pos := 369, limit := 2082 } = .ok (raw.core.codes, { bytes := bytes, pos := 2082, limit := 2082 }) := by
  refine sized_eq_of_parts (size := 1711)
    (payload := { bytes := bytes, pos := 371, limit := 2082 }) (finish := { bytes := bytes, pos := 2082, limit := 2082 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.ByteIO.Artifact
