import Project.ByteIO.ArtifactCache
import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.BinaryParts

namespace Project.ByteIO.Artifact
open Wasm.Binary
attribute [local cbv_opaque] bytes
set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem types_parsed :
    Binary.parseSection 1 funcType { bytes, pos := 8, limit := 2082 } =
      .ok (raw.core.types, { bytes, pos := 71, limit := 2082 }) := by cbv

#print axioms types_parsed

theorem import0_parsed :
    Binary.importEntry { bytes, pos := 75, limit := 299 } =
      .ok (raw.imports[0]!, { bytes, pos := 108, limit := 299 }) := by cbv

theorem import1_parsed :
    Binary.importEntry { bytes, pos := 108, limit := 299 } =
      .ok (raw.imports[1]!, { bytes, pos := 142, limit := 299 }) := by cbv

theorem import2_parsed :
    Binary.importEntry { bytes, pos := 142, limit := 299 } =
      .ok (raw.imports[2]!, { bytes, pos := 187, limit := 299 }) := by cbv

theorem import3_parsed :
    Binary.importEntry { bytes, pos := 187, limit := 299 } =
      .ok (raw.imports[3]!, { bytes, pos := 227, limit := 299 }) := by cbv

theorem import4_parsed :
    Binary.importEntry { bytes, pos := 227, limit := 299 } =
      .ok (raw.imports[4]!, { bytes, pos := 264, limit := 299 }) := by cbv

theorem import5_parsed :
    Binary.importEntry { bytes, pos := 264, limit := 299 } =
      .ok (raw.imports[5]!, { bytes, pos := 299, limit := 299 }) := by cbv

theorem imports_tail6 :
    Internal.vectorLoop Binary.importEntry 0 { bytes, pos := 299, limit := 299 } =
      .ok (raw.imports.drop 6, { bytes, pos := 299, limit := 299 }) := rfl

theorem imports_tail5 :
    Internal.vectorLoop Binary.importEntry 1 { bytes, pos := 264, limit := 299 } =
      .ok (raw.imports.drop 5, { bytes, pos := 299, limit := 299 }) :=
  vectorLoop_eq_cons import5_parsed imports_tail6

theorem imports_tail4 :
    Internal.vectorLoop Binary.importEntry 2 { bytes, pos := 227, limit := 299 } =
      .ok (raw.imports.drop 4, { bytes, pos := 299, limit := 299 }) :=
  vectorLoop_eq_cons import4_parsed imports_tail5

theorem imports_tail3 :
    Internal.vectorLoop Binary.importEntry 3 { bytes, pos := 187, limit := 299 } =
      .ok (raw.imports.drop 3, { bytes, pos := 299, limit := 299 }) :=
  vectorLoop_eq_cons import3_parsed imports_tail4

theorem imports_tail2 :
    Internal.vectorLoop Binary.importEntry 4 { bytes, pos := 142, limit := 299 } =
      .ok (raw.imports.drop 2, { bytes, pos := 299, limit := 299 }) :=
  vectorLoop_eq_cons import2_parsed imports_tail3

theorem imports_tail1 :
    Internal.vectorLoop Binary.importEntry 5 { bytes, pos := 108, limit := 299 } =
      .ok (raw.imports.drop 1, { bytes, pos := 299, limit := 299 }) :=
  vectorLoop_eq_cons import1_parsed imports_tail2

theorem imports_tail0 :
    Internal.vectorLoop Binary.importEntry 6 { bytes, pos := 75, limit := 299 } =
      .ok (raw.imports.drop 0, { bytes, pos := 299, limit := 299 }) :=
  vectorLoop_eq_cons import0_parsed imports_tail1

theorem imports_vector :
    vector Binary.importEntry { bytes, pos := 74, limit := 299 } =
      .ok (raw.imports, { bytes, pos := 299, limit := 299 }) := by
  refine vector_eq_of_parts (length := 6) (itemsStart := { bytes, pos := 75, limit := 299 }) ?_ ?_ imports_tail0
  · cbv
  · decide

theorem imports_sized :
    sized (vector Binary.importEntry) { bytes, pos := 72, limit := 2082 } =
      .ok (raw.imports, { bytes, pos := 299, limit := 2082 }) := by
  refine sized_eq_of_parts (size := 225)
    (payload := { bytes, pos := 74, limit := 2082 }) (finish := { bytes, pos := 299, limit := 299 }) ?_ ?_ ?_ imports_vector ?_
  · cbv
  · decide
  · cbv
  · rfl

theorem imports_parsed :
    Binary.parseSection 2 Binary.importEntry { bytes, pos := 71, limit := 2082 } =
      .ok (raw.imports, { bytes, pos := 299, limit := 2082 }) := by
  refine Binary.parseSection_eq_of_parts (payload := { bytes, pos := 72, limit := 2082 }) ?_ imports_sized
  cbv

#print axioms imports_parsed

theorem functions_parsed :
    Binary.parseSection 3 Leb.u32 { bytes, pos := 299, limit := 2082 } =
      .ok (raw.core.functionTypeIndices, { bytes, pos := 308, limit := 2082 }) := by cbv

#print axioms functions_parsed

theorem memories_parsed :
    Binary.parseSection 5 memoryType { bytes, pos := 308, limit := 2082 } =
      .ok (raw.core.memories, { bytes, pos := 313, limit := 2082 }) := by cbv

#print axioms memories_parsed

theorem globals_parsed :
    Binary.parseSection 6 global { bytes, pos := 313, limit := 2082 } =
      .ok (raw.core.globals, { bytes, pos := 347, limit := 2082 }) := by cbv

#print axioms globals_parsed

theorem exports_parsed :
    Binary.parseSection 7 exportEntry { bytes, pos := 347, limit := 2082 } =
      .ok (raw.core.exports, { bytes, pos := 368, limit := 2082 }) := by cbv

#print axioms exports_parsed

end Project.ByteIO.Artifact
