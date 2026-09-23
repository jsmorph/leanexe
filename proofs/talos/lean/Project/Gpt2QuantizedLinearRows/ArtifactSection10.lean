import Project.Gpt2QuantizedLinearRows.ArtifactByteLookup
import Project.Gpt2QuantizedLinearRows.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.Gpt2QuantizedLinearRows.ArtifactCode0
import Project.Gpt2QuantizedLinearRows.ArtifactCode1
import Project.Gpt2QuantizedLinearRows.ArtifactCode2
import Project.Gpt2QuantizedLinearRows.ArtifactCode3
import Project.Gpt2QuantizedLinearRows.ArtifactCode4
import Project.Gpt2QuantizedLinearRows.ArtifactCode5
import Project.Gpt2QuantizedLinearRows.ArtifactCode6
import Project.Gpt2QuantizedLinearRows.ArtifactCode7
import Project.Gpt2QuantizedLinearRows.ArtifactCode8
import Project.Gpt2QuantizedLinearRows.ArtifactCode9
import Project.Gpt2QuantizedLinearRows.ArtifactCode10
import Project.Gpt2QuantizedLinearRows.ArtifactCode11
import Project.Gpt2QuantizedLinearRows.ArtifactCode12

namespace Project.Gpt2QuantizedLinearRows.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_tail13 :
    Internal.vectorLoop code 0 { bytes := artifactBytes, pos := 4757, limit := 4757 } =
      .ok (Cache.raw.codes.drop 13, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by rfl

theorem codes_tail12 :
    Internal.vectorLoop code 1 { bytes := artifactBytes, pos := 4404, limit := 4757 } =
      .ok (Cache.raw.codes.drop 12, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code12_decoded codes_tail13

theorem codes_tail11 :
    Internal.vectorLoop code 2 { bytes := artifactBytes, pos := 4323, limit := 4757 } =
      .ok (Cache.raw.codes.drop 11, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code11_decoded codes_tail12

theorem codes_tail10 :
    Internal.vectorLoop code 3 { bytes := artifactBytes, pos := 4295, limit := 4757 } =
      .ok (Cache.raw.codes.drop 10, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code10_decoded codes_tail11

theorem codes_tail9 :
    Internal.vectorLoop code 4 { bytes := artifactBytes, pos := 3928, limit := 4757 } =
      .ok (Cache.raw.codes.drop 9, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code9_decoded codes_tail10

theorem codes_tail8 :
    Internal.vectorLoop code 5 { bytes := artifactBytes, pos := 2350, limit := 4757 } =
      .ok (Cache.raw.codes.drop 8, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code8_decoded codes_tail9

theorem codes_tail7 :
    Internal.vectorLoop code 6 { bytes := artifactBytes, pos := 2327, limit := 4757 } =
      .ok (Cache.raw.codes.drop 7, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code7_decoded codes_tail8

theorem codes_tail6 :
    Internal.vectorLoop code 7 { bytes := artifactBytes, pos := 2290, limit := 4757 } =
      .ok (Cache.raw.codes.drop 6, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code6_decoded codes_tail7

theorem codes_tail5 :
    Internal.vectorLoop code 8 { bytes := artifactBytes, pos := 2267, limit := 4757 } =
      .ok (Cache.raw.codes.drop 5, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code5_decoded codes_tail6

theorem codes_tail4 :
    Internal.vectorLoop code 9 { bytes := artifactBytes, pos := 2002, limit := 4757 } =
      .ok (Cache.raw.codes.drop 4, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code4_decoded codes_tail5

theorem codes_tail3 :
    Internal.vectorLoop code 10 { bytes := artifactBytes, pos := 846, limit := 4757 } =
      .ok (Cache.raw.codes.drop 3, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code3_decoded codes_tail4

theorem codes_tail2 :
    Internal.vectorLoop code 11 { bytes := artifactBytes, pos := 743, limit := 4757 } =
      .ok (Cache.raw.codes.drop 2, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code2_decoded codes_tail3

theorem codes_tail1 :
    Internal.vectorLoop code 12 { bytes := artifactBytes, pos := 394, limit := 4757 } =
      .ok (Cache.raw.codes.drop 1, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code1_decoded codes_tail2

theorem codes_tail0 :
    Internal.vectorLoop code 13 { bytes := artifactBytes, pos := 305, limit := 4757 } =
      .ok (Cache.raw.codes.drop 0, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  exact vectorLoop_eq_cons code0_decoded codes_tail1

theorem codes_vector_decoded :
    vector code { bytes := artifactBytes, pos := 304, limit := 4757 } =
      .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  refine vector_eq_of_parts (length := 13)
    (itemsStart := { bytes := artifactBytes, pos := 305, limit := 4757 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact codes_tail0

theorem codes_section_decoded :
    sized (vector code) { bytes := artifactBytes, pos := 302, limit := 4757 } = .ok (Cache.raw.codes, { bytes := artifactBytes, pos := 4757, limit := 4757 }) := by
  refine sized_eq_of_parts (size := 4453)
    (payload := { bytes := artifactBytes, pos := 304, limit := 4757 }) (finish := { bytes := artifactBytes, pos := 4757, limit := 4757 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact codes_vector_decoded
  · rfl

#print axioms codes_section_decoded

end Project.Gpt2QuantizedLinearRows.Artifact
