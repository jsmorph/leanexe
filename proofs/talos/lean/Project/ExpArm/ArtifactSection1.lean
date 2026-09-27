import Project.ExpArm.ArtifactByteLookup
import Project.ExpArm.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.ExpArm.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type0_decoded :
    funcType { bytes := artifactBytes, pos := 11, limit := 45 } =
      .ok (Cache.raw.types[0]!, { bytes := artifactBytes, pos := 16, limit := 45 }) := by cbv

#print axioms type0_decoded

theorem type1_decoded :
    funcType { bytes := artifactBytes, pos := 16, limit := 45 } =
      .ok (Cache.raw.types[1]!, { bytes := artifactBytes, pos := 23, limit := 45 }) := by cbv

#print axioms type1_decoded

theorem type2_decoded :
    funcType { bytes := artifactBytes, pos := 23, limit := 45 } =
      .ok (Cache.raw.types[2]!, { bytes := artifactBytes, pos := 28, limit := 45 }) := by cbv

#print axioms type2_decoded

theorem type3_decoded :
    funcType { bytes := artifactBytes, pos := 28, limit := 45 } =
      .ok (Cache.raw.types[3]!, { bytes := artifactBytes, pos := 33, limit := 45 }) := by cbv

#print axioms type3_decoded

theorem type4_decoded :
    funcType { bytes := artifactBytes, pos := 33, limit := 45 } =
      .ok (Cache.raw.types[4]!, { bytes := artifactBytes, pos := 36, limit := 45 }) := by cbv

#print axioms type4_decoded

theorem type5_decoded :
    funcType { bytes := artifactBytes, pos := 36, limit := 45 } =
      .ok (Cache.raw.types[5]!, { bytes := artifactBytes, pos := 41, limit := 45 }) := by cbv

#print axioms type5_decoded

theorem type6_decoded :
    funcType { bytes := artifactBytes, pos := 41, limit := 45 } =
      .ok (Cache.raw.types[6]!, { bytes := artifactBytes, pos := 45, limit := 45 }) := by cbv

#print axioms type6_decoded

theorem types_tail7 :
    Internal.vectorLoop funcType 0 { bytes := artifactBytes, pos := 45, limit := 45 } =
      .ok (Cache.raw.types.drop 7, { bytes := artifactBytes, pos := 45, limit := 45 }) := by rfl

theorem types_tail6 :
    Internal.vectorLoop funcType 1 { bytes := artifactBytes, pos := 41, limit := 45 } =
      .ok (Cache.raw.types.drop 6, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type6_decoded types_tail7

theorem types_tail5 :
    Internal.vectorLoop funcType 2 { bytes := artifactBytes, pos := 36, limit := 45 } =
      .ok (Cache.raw.types.drop 5, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type5_decoded types_tail6

theorem types_tail4 :
    Internal.vectorLoop funcType 3 { bytes := artifactBytes, pos := 33, limit := 45 } =
      .ok (Cache.raw.types.drop 4, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type4_decoded types_tail5

theorem types_tail3 :
    Internal.vectorLoop funcType 4 { bytes := artifactBytes, pos := 28, limit := 45 } =
      .ok (Cache.raw.types.drop 3, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type3_decoded types_tail4

theorem types_tail2 :
    Internal.vectorLoop funcType 5 { bytes := artifactBytes, pos := 23, limit := 45 } =
      .ok (Cache.raw.types.drop 2, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type2_decoded types_tail3

theorem types_tail1 :
    Internal.vectorLoop funcType 6 { bytes := artifactBytes, pos := 16, limit := 45 } =
      .ok (Cache.raw.types.drop 1, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type1_decoded types_tail2

theorem types_tail0 :
    Internal.vectorLoop funcType 7 { bytes := artifactBytes, pos := 11, limit := 45 } =
      .ok (Cache.raw.types.drop 0, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  exact vectorLoop_eq_cons type0_decoded types_tail1

theorem types_vector_decoded :
    vector funcType { bytes := artifactBytes, pos := 10, limit := 45 } =
      .ok (Cache.raw.types, { bytes := artifactBytes, pos := 45, limit := 45 }) := by
  refine vector_eq_of_parts (length := 7)
    (itemsStart := { bytes := artifactBytes, pos := 11, limit := 45 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact types_tail0

theorem types_section_decoded :
    sized (vector funcType) { bytes := artifactBytes, pos := 9, limit := 12733 } = .ok (Cache.raw.types, { bytes := artifactBytes, pos := 45, limit := 12733 }) := by
  refine sized_eq_of_parts (size := 35)
    (payload := { bytes := artifactBytes, pos := 10, limit := 12733 }) (finish := { bytes := artifactBytes, pos := 45, limit := 45 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact types_vector_decoded
  · rfl

#print axioms types_section_decoded

end Project.ExpArm.Artifact
