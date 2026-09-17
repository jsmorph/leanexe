import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem globals_item0 :
    global { bytes := artifactBytes, pos := 909, limit := 940 } =
      .ok (Cache.raw.globals[0]!, { bytes := artifactBytes, pos := 915, limit := 940 }) := by cbv

theorem globals_item1 :
    global { bytes := artifactBytes, pos := 915, limit := 940 } =
      .ok (Cache.raw.globals[1]!, { bytes := artifactBytes, pos := 920, limit := 940 }) := by cbv

theorem globals_item2 :
    global { bytes := artifactBytes, pos := 920, limit := 940 } =
      .ok (Cache.raw.globals[2]!, { bytes := artifactBytes, pos := 925, limit := 940 }) := by cbv

theorem globals_item3 :
    global { bytes := artifactBytes, pos := 925, limit := 940 } =
      .ok (Cache.raw.globals[3]!, { bytes := artifactBytes, pos := 930, limit := 940 }) := by cbv

theorem globals_item4 :
    global { bytes := artifactBytes, pos := 930, limit := 940 } =
      .ok (Cache.raw.globals[4]!, { bytes := artifactBytes, pos := 935, limit := 940 }) := by cbv

theorem globals_item5 :
    global { bytes := artifactBytes, pos := 935, limit := 940 } =
      .ok (Cache.raw.globals[5]!, { bytes := artifactBytes, pos := 940, limit := 940 }) := by cbv

theorem globals_tail6 :
    Internal.vectorLoop global 0 { bytes := artifactBytes, pos := 940, limit := 940 } =
      .ok (Cache.raw.globals.drop 6, { bytes := artifactBytes, pos := 940, limit := 940 }) := by rfl

theorem globals_tail5 :
    Internal.vectorLoop global 1 { bytes := artifactBytes, pos := 935, limit := 940 } =
      .ok (Cache.raw.globals.drop 5, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  exact vectorLoop_eq_cons globals_item5 globals_tail6

theorem globals_tail4 :
    Internal.vectorLoop global 2 { bytes := artifactBytes, pos := 930, limit := 940 } =
      .ok (Cache.raw.globals.drop 4, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  exact vectorLoop_eq_cons globals_item4 globals_tail5

theorem globals_tail3 :
    Internal.vectorLoop global 3 { bytes := artifactBytes, pos := 925, limit := 940 } =
      .ok (Cache.raw.globals.drop 3, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  exact vectorLoop_eq_cons globals_item3 globals_tail4

theorem globals_tail2 :
    Internal.vectorLoop global 4 { bytes := artifactBytes, pos := 920, limit := 940 } =
      .ok (Cache.raw.globals.drop 2, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  exact vectorLoop_eq_cons globals_item2 globals_tail3

theorem globals_tail1 :
    Internal.vectorLoop global 5 { bytes := artifactBytes, pos := 915, limit := 940 } =
      .ok (Cache.raw.globals.drop 1, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  exact vectorLoop_eq_cons globals_item1 globals_tail2

theorem globals_tail0 :
    Internal.vectorLoop global 6 { bytes := artifactBytes, pos := 909, limit := 940 } =
      .ok (Cache.raw.globals.drop 0, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  exact vectorLoop_eq_cons globals_item0 globals_tail1

theorem globals_vector :
    vector global { bytes := artifactBytes, pos := 908, limit := 940 } = .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 940, limit := 940 }) := by
  refine vector_eq_of_parts (length := 6) (itemsStart := { bytes := artifactBytes, pos := 909, limit := 940 }) ?_ ?_ globals_tail0
  · cbv
  · decide

theorem globals_section_decoded :
    sized (vector global) { bytes := artifactBytes, pos := 907, limit := 16006 } = .ok (Cache.raw.globals, { bytes := artifactBytes, pos := 940, limit := 16006 }) := by
  refine sized_eq_of_parts (size := 32) (payload := { bytes := artifactBytes, pos := 908, limit := 16006 })
    (finish := { bytes := artifactBytes, pos := 940, limit := 940 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact globals_vector
  · rfl

#print axioms globals_section_decoded
end Project.TinyGpt2Hidden.Artifact
