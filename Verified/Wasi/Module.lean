import Verified.Wasi.ABI
import Verified.Wasi.Relocation

namespace Verified.Wasi.Module

open Wasm

/-- Extra functions use final call and type indices.  Export indices refer to `funcs`. -/
structure Extension where
  types : List FuncType := []
  funcs : List Function := []
  exports : List Export := []

def pureIndex (index : Nat) : Nat := 3 + index

def extraIndex (source : Wasm.Module) (index : Nat) : Nat := 3 + source.funcs.length + index

def extraTypeIndex (source : Wasm.Module) (index : Nat) : Nat := 3 + source.types.length + index

def pureExport (entry : Export) : Export :=
  { entry with funcIdx := pureIndex entry.funcIdx }

def extraExport (source : Wasm.Module) (entry : Export) : Export :=
  { entry with funcIdx := extraIndex source entry.funcIdx }

def assemble (source : Wasm.Module) (extra : Extension) : Wasm.Module :=
  let types := ABI.types ++ source.types ++ extra.types
  { source with
    imports := ABI.imports
    types
    gcTypes := types.map fun type => { comp := .func type }
    funcs := source.funcs.map Relocation.function ++ extra.funcs
    exports := source.exports.map pureExport ++ extra.exports.map (extraExport source)
    tables := [ABI.functionTable]
    tableExports := ABI.tableExports }

@[simp] theorem imports (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).imports = ABI.imports := rfl

@[simp] theorem types (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).types = ABI.types ++ source.types ++ extra.types := rfl

@[simp] theorem funcs (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).funcs = source.funcs.map Relocation.function ++ extra.funcs := rfl

@[simp] theorem funcs_length (source : Wasm.Module) (extra : Extension) :
    (assemble source extra).funcs.length = source.funcs.length + extra.funcs.length := by
  simp only [funcs, List.length_append, List.length_map]

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
    (assemble source extra).funcs[index]? = some (Relocation.function func) := by
  have hIndex := (List.getElem?_eq_some_iff.mp h).1
  rw [funcs, List.getElem?_append_left (by simpa only [List.length_map] using hIndex)]
  simp only [List.getElem?_map, h, Option.map_some]

theorem extra_function (source : Wasm.Module) (extra : Extension) (index : Nat) :
    (assemble source extra).funcs[source.funcs.length + index]? = extra.funcs[index]? := by
  rw [funcs, List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]

theorem pure_type {source : Wasm.Module} (extra : Extension) {index : Nat} {type : FuncType}
    (h : source.types[index]? = some type) :
    (assemble source extra).types[3 + index]? = some type := by
  have hIndex := (List.getElem?_eq_some_iff.mp h).1
  rw [types, List.append_assoc, List.getElem?_append_right (by rw [ABI.types_length]; omega),
    ABI.types_length, Nat.add_sub_cancel_left, List.getElem?_append_left hIndex]
  exact h

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
        some (Encoding.Spec.signature (Relocation.function func)) := by
  refine ⟨?_, ?_⟩
  · simp only [Relocation.function, hIndex, Option.map_some]
  · rw [pure_function_signature]
    exact pure_type extra hType

theorem extra_type_index (source : Wasm.Module) (extra : Extension) (index : Nat) :
    (assemble source extra).types[extraTypeIndex source index]? = extra.types[index]? :=
  extra_type source extra index

theorem pure_export {source : Wasm.Module} (extra : Extension) {entry : Export}
    (h : entry ∈ source.exports) : pureExport entry ∈ (assemble source extra).exports :=
  List.mem_append_left _ (List.mem_map.mpr ⟨entry, h, rfl⟩)

theorem extra_export (source : Wasm.Module) {extra : Extension} {entry : Export}
    (h : entry ∈ extra.exports) : extraExport source entry ∈ (assemble source extra).exports :=
  List.mem_append_right _ (List.mem_map.mpr ⟨entry, h, rfl⟩)

theorem pure_index_valid (source : Wasm.Module) (extra : Extension) {index : Nat}
    (h : index < source.funcs.length) :
    pureIndex index < (assemble source extra).imports.length +
      (assemble source extra).funcs.length := by
  simp only [pureIndex, imports, ABI.imports_length, funcs_length]
  omega

theorem extra_index_valid (source : Wasm.Module) (extra : Extension) {index : Nat}
    (h : index < extra.funcs.length) :
    extraIndex source index < (assemble source extra).imports.length +
      (assemble source extra).funcs.length := by
  simp only [extraIndex, imports, ABI.imports_length, funcs_length]
  omega

theorem pure_dispatch_index (source : Wasm.Module) (extra : Extension) (index : Nat) :
    pureIndex index - (assemble source extra).imports.length = index := by
  simp only [pureIndex, imports, ABI.imports_length]
  omega

theorem extra_dispatch_index (source : Wasm.Module) (extra : Extension) (index : Nat) :
    extraIndex source index - (assemble source extra).imports.length =
      source.funcs.length + index := by
  simp only [extraIndex, imports, ABI.imports_length]
  omega

theorem layout (source : Wasm.Module) (extra : Extension) (hImports : source.imports = []) :
    Relocation.Layout source (assemble source extra) :=
  { sourceImports := hImports
    targetImports := ABI.imports_length
    functions := pure_function extra
    memory64 := rfl
    memoryCap := rfl }

theorem shape (source : Wasm.Module) (extra : Extension) (h : Encoding.Spec.Shape source) :
    Encoding.Spec.Shape (assemble source extra) :=
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

theorem allocator_index : pureIndex 0 = 3 := rfl

theorem release_index : pureIndex 1 = 4 := rfl

end Verified.Wasi.Module
