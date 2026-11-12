import Verified.Wasi.ABI
import Verified.Wasi.Relocation

/-!
Assembly of a WASI module from the pure module and an extension.  `assembleWith calls` imports the
three stream functions and then the flat calls `calls`; every defined function follows at
`(3 + calls.length)`, and the calls' import types follow every other type.  The forms without
`With` are those of a module without calls.
-/

namespace Verified.Wasi.Module

open Wasm LeanExe.Wasi

/-- Extra functions use final call and type indices.  Export indices refer to `funcs`. -/
structure Extension where
  types : List FuncType := []
  funcs : List Function := []
  exports : List Export := []

def pureIndexWith (calls : List Call) (index : Nat) : Nat := (3 + calls.length) + index

def pureIndex (index : Nat) : Nat := pureIndexWith [] index

def extraIndexWith (calls : List Call) (source : Wasm.Module) (index : Nat) : Nat :=
  (3 + calls.length) + source.funcs.length + index

def extraIndex (source : Wasm.Module) (index : Nat) : Nat := extraIndexWith [] source index

def extraTypeIndex (source : Wasm.Module) (index : Nat) : Nat := 3 + source.types.length + index

def pureExportWith (calls : List Call) (entry : Export) : Export :=
  { entry with funcIdx := pureIndexWith calls entry.funcIdx }

def pureExport (entry : Export) : Export := pureExportWith [] entry

def extraExportWith (calls : List Call) (source : Wasm.Module) (entry : Export) : Export :=
  { entry with funcIdx := extraIndexWith calls source entry.funcIdx }

def extraExport (source : Wasm.Module) (entry : Export) : Export := extraExportWith [] source entry

def assembleWith (calls : List Call) (source : Wasm.Module) (extra : Extension) : Wasm.Module :=
  let types := ABI.withCallTypes (ABI.types ++ source.types ++ extra.types) calls
  { source with
    imports := ABI.importsWith calls
    types
    gcTypes := types.map fun type => { comp := .func type }
    funcs := source.funcs.map (Relocation.functionWith calls) ++ extra.funcs
    exports := source.exports.map (pureExportWith calls) ++
      extra.exports.map (extraExportWith calls source)
    tables := [ABI.functionTable]
    tableExports := ABI.tableExports }

def assemble (source : Wasm.Module) (extra : Extension) : Wasm.Module := assembleWith [] source extra

section General

variable {calls : List Call}

@[simp] theorem imports_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).imports = ABI.importsWith calls := rfl

@[simp] theorem imports_length_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).imports.length = (3 + calls.length) := by
  simp only [imports_with, ABI.importsWith_length]

@[simp] theorem types_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).types =
      ABI.types ++ source.types ++ extra.types ++ calls.map ABI.callType := by
  simp only [assembleWith, ABI.withCallTypes_eq]

@[simp] theorem funcs_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).funcs =
      source.funcs.map (Relocation.functionWith calls) ++ extra.funcs := rfl

@[simp] theorem funcs_length_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).funcs.length = source.funcs.length + extra.funcs.length := by
  simp only [funcs_with, List.length_append, List.length_map]

@[simp] theorem memory_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).memory = source.memory := rfl

@[simp] theorem globals_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).globals = source.globals := rfl

@[simp] theorem memory64_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).memIs64 = source.memIs64 := rfl

@[simp] theorem memoryCap_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).memoryCap = source.memoryCap := rfl

@[simp] theorem dataSegments_with (source : Wasm.Module) (extra : Extension) :
    Encoding.Spec.dataSegments (assembleWith calls source extra) =
      Encoding.Spec.dataSegments source := rfl

@[simp] theorem tables_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).tables = [ABI.functionTable] := rfl

@[simp] theorem tableExports_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).tableExports = ABI.tableExports := rfl

@[simp] theorem globalExports_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).globalExports = source.globalExports := rfl

@[simp] theorem memoryExports_with (source : Wasm.Module) (extra : Extension) :
    (assembleWith calls source extra).memoryExports = source.memoryExports := rfl

theorem pure_function_with {source : Wasm.Module} (extra : Extension) {index : Nat}
    {func : Function} (h : source.funcs[index]? = some func) :
    (assembleWith calls source extra).funcs[index]? = some (Relocation.functionWith calls func) := by
  have hIndex := (List.getElem?_eq_some_iff.mp h).1
  rw [funcs_with, List.getElem?_append_left (by simpa only [List.length_map] using hIndex)]
  simp only [List.getElem?_map, h, Option.map_some]

theorem extra_function_with (source : Wasm.Module) (extra : Extension) (index : Nat) :
    (assembleWith calls source extra).funcs[source.funcs.length + index]? = extra.funcs[index]? := by
  rw [funcs_with, List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]

theorem pure_type_with {source : Wasm.Module} (extra : Extension) {index : Nat} {type : FuncType}
    (h : source.types[index]? = some type) :
    (assembleWith calls source extra).types[3 + index]? = some type := by
  have hIndex := (List.getElem?_eq_some_iff.mp h).1
  rw [types_with, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [ABI.types_length]; omega), ABI.types_length,
    Nat.add_sub_cancel_left, List.getElem?_append_left hIndex]
  exact h

theorem extra_type_with (source : Wasm.Module) (extra : Extension) (index : Nat)
    (hIndex : index < extra.types.length) :
    (assembleWith calls source extra).types[3 + source.types.length + index]? =
      extra.types[index]? := by
  rw [types_with, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by rw [ABI.types_length]; omega), ABI.types_length]
  rw [show 3 + source.types.length + index - 3 = source.types.length + index by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hIndex]

theorem pure_function_type_with {source : Wasm.Module} (extra : Extension)
    {func : Function} {index : Nat} (hIndex : func.typeIdx = some index)
    (hType : source.types[index]? = some (Encoding.Spec.signature func)) :
    (Relocation.functionWith calls func).typeIdx = some (3 + index) ∧
      (assembleWith calls source extra).types[3 + index]? =
        some (Encoding.Spec.signature (Relocation.functionWith calls func)) := by
  refine ⟨?_, ?_⟩
  · simp only [Relocation.functionWith, hIndex, Option.map_some]
  · exact pure_type_with extra hType

theorem extra_type_index_with (source : Wasm.Module) (extra : Extension) (index : Nat)
    (hIndex : index < extra.types.length) :
    (assembleWith calls source extra).types[extraTypeIndex source index]? = extra.types[index]? :=
  extra_type_with source extra index hIndex

theorem pure_export_with {source : Wasm.Module} (extra : Extension) {entry : Export}
    (h : entry ∈ source.exports) :
    pureExportWith calls entry ∈ (assembleWith calls source extra).exports :=
  List.mem_append_left _ (List.mem_map.mpr ⟨entry, h, rfl⟩)

theorem extra_export_with (source : Wasm.Module) {extra : Extension} {entry : Export}
    (h : entry ∈ extra.exports) :
    extraExportWith calls source entry ∈ (assembleWith calls source extra).exports :=
  List.mem_append_right _ (List.mem_map.mpr ⟨entry, h, rfl⟩)

theorem pure_index_valid_with (source : Wasm.Module) (extra : Extension) {index : Nat}
    (h : index < source.funcs.length) :
    pureIndexWith calls index < (assembleWith calls source extra).imports.length +
      (assembleWith calls source extra).funcs.length := by
  simp only [pureIndexWith, imports_length_with, funcs_length_with]
  omega

theorem extra_index_valid_with (source : Wasm.Module) (extra : Extension) {index : Nat}
    (h : index < extra.funcs.length) :
    extraIndexWith calls source index < (assembleWith calls source extra).imports.length +
      (assembleWith calls source extra).funcs.length := by
  simp only [extraIndexWith, imports_length_with, funcs_length_with]
  omega

theorem pure_dispatch_index_with (source : Wasm.Module) (extra : Extension) (index : Nat) :
    pureIndexWith calls index - (assembleWith calls source extra).imports.length = index := by
  simp only [pureIndexWith, imports_length_with]
  omega

theorem extra_dispatch_index_with (source : Wasm.Module) (extra : Extension) (index : Nat) :
    extraIndexWith calls source index - (assembleWith calls source extra).imports.length =
      source.funcs.length + index := by
  simp only [extraIndexWith, imports_length_with]
  omega

theorem layout_with (source : Wasm.Module) (extra : Extension) (hImports : source.imports = []) :
    Relocation.LayoutWith calls source (assembleWith calls source extra) :=
  { sourceImports := hImports
    targetImports := imports_length_with source extra
    functions := pure_function_with extra
    memory64 := rfl
    memoryCap := rfl }

theorem shape_with (source : Wasm.Module) (extra : Extension) (h : Encoding.Spec.Shape source) :
    Encoding.Spec.Shape (assembleWith calls source extra) :=
  { extraMemories := h.extraMemories
    dataWithoutMemory := h.dataWithoutMemory
    start := h.start
    gcTypes := rfl
    tables := Or.inr rfl
    elements := h.elements
    importedGlobals := h.importedGlobals
    importedTables := h.importedTables
    importedMemories := h.importedMemories
    importedTags := h.importedTags
    tableExports := rfl
    tagExports := h.tagExports
    tags := h.tags }

theorem allocator_index_with : pureIndexWith calls 0 = (3 + calls.length) := rfl

theorem release_index_with : pureIndexWith calls 1 = (3 + calls.length) + 1 := rfl

end General

@[simp] theorem imports (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).imports = ABI.imports := rfl

@[simp] theorem types (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).types = ABI.types ++ source.types ++ extra.types := rfl

@[simp] theorem funcs (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).funcs = source.funcs.map Relocation.function ++ extra.funcs := rfl

@[simp] theorem funcs_length (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).funcs.length = source.funcs.length + extra.funcs.length :=
  funcs_length_with source extra

@[simp] theorem memory (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).memory = source.memory := rfl

@[simp] theorem globals (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).globals = source.globals := rfl

@[simp] theorem memory64 (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).memIs64 = source.memIs64 := rfl

@[simp] theorem memoryCap (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).memoryCap = source.memoryCap := rfl

@[simp] theorem dataSegments (source : Wasm.Module) (extra : Extension) :
    Encoding.Spec.dataSegments (assemble source extra) = Encoding.Spec.dataSegments source := rfl

@[simp] theorem tables (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).tables = [ABI.functionTable] := rfl

@[simp] theorem tableExports (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).tableExports = ABI.tableExports := rfl

@[simp] theorem globalExports (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).globalExports = source.globalExports := rfl

@[simp] theorem memoryExports (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).memoryExports = source.memoryExports := rfl

theorem pure_function {source : Wasm.Module} (extra : Extension) {index : Nat} {func : Function}
    (h : source.funcs[index]? = some func) :
    (assemble source extra).funcs[index]? = some (Relocation.function func) :=
  pure_function_with extra h

theorem extra_function (source : Wasm.Module) (extra : Extension) (index : Nat) :
    (assemble source extra).funcs[source.funcs.length + index]? = extra.funcs[index]? :=
  extra_function_with source extra index

theorem pure_type {source : Wasm.Module} (extra : Extension) {index : Nat} {type : FuncType}
    (h : source.types[index]? = some type) :
    (assemble source extra).types[3 + index]? = some type :=
  pure_type_with extra h

theorem extra_type (source : Wasm.Module) (extra : Extension) (index : Nat) :
    (assemble source extra).types[3 + source.types.length + index]? = extra.types[index]? := by
  rw [types, List.append_assoc,
    List.getElem?_append_right (by rw [ABI.types_length]; omega), ABI.types_length]
  rw [show 3 + source.types.length + index - 3 = source.types.length + index by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem pure_function_signature (func : Function) :
    Encoding.Spec.signature (Relocation.function func) = Encoding.Spec.signature func := rfl

theorem pure_function_type {source : Wasm.Module} (extra : Extension)
    {func : Function} {index : Nat} (hIndex : func.typeIdx = some index)
    (hType : source.types[index]? = some (Encoding.Spec.signature func)) :
    (Relocation.function func).typeIdx = some (3 + index) ∧
      (assemble source extra).types[3 + index]? =
        some (Encoding.Spec.signature (Relocation.function func)) :=
  pure_function_type_with extra hIndex hType

theorem extra_type_index (source : Wasm.Module) (extra : Extension) (index : Nat) :
    (assemble source extra).types[extraTypeIndex source index]? = extra.types[index]? :=
  extra_type source extra index

theorem pure_export {source : Wasm.Module} (extra : Extension) {entry : Export}
    (h : entry ∈ source.exports) : pureExport entry ∈ (assemble source extra).exports :=
  pure_export_with extra h

theorem extra_export (source : Wasm.Module) {extra : Extension} {entry : Export}
    (h : entry ∈ extra.exports) : extraExport source entry ∈ (assemble source extra).exports :=
  extra_export_with source h

theorem pure_index_valid (source : Wasm.Module) (extra : Extension) {index : Nat}
    (h : index < source.funcs.length) :
    pureIndex index < (assemble source extra).imports.length +
      (assemble source extra).funcs.length :=
  pure_index_valid_with source extra h

theorem extra_index_valid (source : Wasm.Module) (extra : Extension) {index : Nat}
    (h : index < extra.funcs.length) :
    extraIndex source index < (assemble source extra).imports.length +
      (assemble source extra).funcs.length :=
  extra_index_valid_with source extra h

theorem pure_dispatch_index (source : Wasm.Module) (extra : Extension) (index : Nat) :
    pureIndex index - (assemble source extra).imports.length = index :=
  pure_dispatch_index_with source extra index

theorem extra_dispatch_index (source : Wasm.Module) (extra : Extension) (index : Nat) :
    extraIndex source index - (assemble source extra).imports.length =
      source.funcs.length + index :=
  extra_dispatch_index_with source extra index

theorem layout (source : Wasm.Module) (extra : Extension) (hImports : source.imports = []) :
    Relocation.Layout source (assemble source extra) :=
  let general := layout_with (calls := []) source extra hImports
  ⟨general.sourceImports, general.targetImports, general.functions, general.memory64,
    general.memoryCap⟩

theorem shape (source : Wasm.Module) (extra : Extension) (h : Encoding.Spec.Shape source) :
    Encoding.Spec.Shape (assemble source extra) :=
  shape_with source extra h

theorem allocator_index : pureIndex 0 = 3 := rfl

theorem release_index : pureIndex 1 = 4 := rfl

end Verified.Wasi.Module
