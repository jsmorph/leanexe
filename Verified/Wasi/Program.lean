import Verified.Wasi.ProgramIndex

namespace Verified.Wasi

open Wasm

def EffectProg.callableExtensionWith (calls : List LeanExe.Wasi.Call) (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) : Module.Extension :=
  { types := program.types ++ entries.map EffectEntry.type
    funcs := program.functionsWith calls source pool ++ entries.mapIdx (fun index entry =>
      entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index)))
    exports := entries.mapIdx fun index entry =>
      { name := entry.signature.name, funcIdx := effectSigs.length + index } }

def EffectProg.callableExtension (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) : Module.Extension :=
  EffectProg.callableExtensionWith [] source program entries pool

def EffectProg.commandExtensionWith (calls : List LeanExe.Wasi.Call) (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) : Module.Extension :=
  { types := program.types ++ [startType]
    funcs := program.functionsWith calls source pool ++
      [main.functionWith calls source (effectTypeIndex source effectSigs.length)]
    exports := [{ name := "_start", funcIdx := effectSigs.length }] }

def EffectProg.commandExtension (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) : Module.Extension :=
  EffectProg.commandExtensionWith [] source program main pool

/-- The WASI module of `program` that imports the flat calls `calls` after the stream imports. -/
def compileCalls (calls : List LeanExe.Wasi.Call) (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs) := none)
    (pool : Bytes.LiteralPool) : Wasm.Module :=
  let next := match main with
    | none => program.callableExtensionWith calls source entries pool
    | some entry => program.commandExtensionWith calls source entry pool
  let assembled := Module.assembleWith calls source (Wrappers.extensionWith calls source next)
  { assembled with
    exports := (match main with
      | none => [{ name := "alloc", funcIdx := Module.pureIndexWith calls 0 },
          { name := "release", funcIdx := Module.pureIndexWith calls 1 }]
      | some _ => []) ++
      next.exports.map (fun entry =>
        { entry with funcIdx := Wrappers.effectIndexWith calls source entry.funcIdx })
    globalExports := match main with
      | none => source.globalExports
      | some _ => []
    memoryExports := [("memory", 0)] }

def compile (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs) := none)
    (pool : Bytes.LiteralPool) : Wasm.Module :=
  compileCalls [] source program entries main pool

theorem EffectProg.callableExtension_types_length_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (program.callableExtensionWith calls source entries pool).types.length =
      effectSigs.length + entries.length := by
  simp only [EffectProg.callableExtensionWith, List.length_append, List.length_map,
    EffectProg.types_length]

theorem EffectProg.callableExtension_types_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).types.length =
      effectSigs.length + entries.length := by
  layout_instance EffectProg.callableExtension_types_length_with

theorem EffectProg.callableExtension_funcs_length_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (program.callableExtensionWith calls source entries pool).funcs.length =
      effectSigs.length + entries.length := by
  simp only [EffectProg.callableExtensionWith, List.length_append, List.length_mapIdx,
    program.functions_length_with source pool]

theorem EffectProg.callableExtension_funcs_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).funcs.length =
      effectSigs.length + entries.length := by
  layout_instance EffectProg.callableExtension_funcs_length_with

theorem EffectProg.commandExtension_types_length_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtensionWith calls source main pool).types.length = effectSigs.length + 1 := by
  simp only [EffectProg.commandExtensionWith, List.length_append, List.length_cons, List.length_nil,
    EffectProg.types_length]

theorem EffectProg.commandExtension_types_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).types.length = effectSigs.length + 1 := by
  layout_instance EffectProg.commandExtension_types_length_with

theorem EffectProg.commandExtension_funcs_length_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtensionWith calls source main pool).funcs.length = effectSigs.length + 1 := by
  simp only [EffectProg.commandExtensionWith, List.length_append, List.length_cons, List.length_nil,
    program.functions_length_with source pool]

theorem EffectProg.commandExtension_funcs_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).funcs.length = effectSigs.length + 1 := by
  layout_instance EffectProg.commandExtension_funcs_length_with

theorem EffectProg.callableExtension_body_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (program.callableExtensionWith calls source entries pool).funcs[index]? =
      (program.functionsWith calls source pool)[index]? := by
  exact List.getElem?_append_left (by rw [program.functions_length_with source pool]; exact hIndex)

theorem EffectProg.callableExtension_body (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).funcs[index]? =
      (program.functions source pool)[index]? := by
  layout_instance EffectProg.callableExtension_body_with

theorem EffectProg.callableExtension_entry_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (index : Nat) (pool : Bytes.LiteralPool) :
    (program.callableExtensionWith calls source entries pool).funcs[effectSigs.length + index]? =
      (entries[index]?).map (fun entry =>
        entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index))) := by
  rw [EffectProg.callableExtensionWith,
    List.getElem?_append_right (by rw [program.functions_length_with source pool]; omega),
    program.functions_length_with source pool, Nat.add_sub_cancel_left, List.getElem?_mapIdx]

theorem EffectProg.callableExtension_entry (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (index : Nat) (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).funcs[effectSigs.length + index]? =
      (entries[index]?).map (fun entry =>
        entry.function source (effectTypeIndex source (effectSigs.length + index))) := by
  layout_instance EffectProg.callableExtension_entry_with

theorem EffectProg.commandExtension_body_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (program.commandExtensionWith calls source main pool).funcs[index]? =
      (program.functionsWith calls source pool)[index]? := by
  exact List.getElem?_append_left (by rw [program.functions_length_with source pool]; exact hIndex)

theorem EffectProg.commandExtension_body (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).funcs[index]? =
      (program.functions source pool)[index]? := by
  layout_instance EffectProg.commandExtension_body_with

theorem EffectProg.commandExtension_start_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtensionWith calls source main pool).funcs[effectSigs.length]? =
      some (main.functionWith calls source (effectTypeIndex source effectSigs.length)) := by
  rw [EffectProg.commandExtensionWith,
    List.getElem?_append_right (by rw [program.functions_length_with source pool]),
    program.functions_length_with source pool, Nat.sub_self]
  rfl

theorem EffectProg.commandExtension_start (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).funcs[effectSigs.length]? =
      some (main.function source (effectTypeIndex source effectSigs.length)) := by
  layout_instance EffectProg.commandExtension_start_with

theorem Wrappers.next_type_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (next : Module.Extension) (index : Nat)
    (hIndex : index < next.types.length) :
    (Module.assembleWith calls source (Wrappers.extensionWith calls source next)).types[
      effectTypeIndex source index]? = next.types[index]? := by
  rw [effectTypeIndex, Module.extra_type_index_with _ _ _
    (by simp only [Wrappers.extensionWith, List.length_append, List.length_cons, List.length_nil]
        omega)]
  change (Wrappers.readType :: Wrappers.writeType :: next.types)[2 + index]? = _
  rw [Nat.add_comm 2 index]
  rfl

theorem Wrappers.next_type (source : Wasm.Module) (next : Module.Extension) (index : Nat) :
    (Module.assemble source (Wrappers.extension source next)).types[
      effectTypeIndex source index]? = next.types[index]? := by
  rw [effectTypeIndex, Module.extra_type_index]
  change (Wrappers.readType :: Wrappers.writeType :: next.types)[2 + index]? = _
  rw [Nat.add_comm 2 index]
  rfl

theorem compile_body_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).funcs[source.funcs.length + (3 + index)]? =
      (program.functionsWith calls source pool)[index]? := by
  cases main with
  | none =>
    change (Module.assembleWith calls source (Wrappers.extensionWith calls source
      (program.callableExtensionWith calls source entries pool))).funcs[
        source.funcs.length + (3 + index)]? = (program.functionsWith calls source pool)[index]?
    rw [Wrappers.next_function_with]
    exact program.callableExtension_body_with source entries hIndex pool
  | some main =>
    change (Module.assembleWith calls source (Wrappers.extensionWith calls source
      (program.commandExtensionWith calls source main pool))).funcs[
        source.funcs.length + (3 + index)]? = (program.functionsWith calls source pool)[index]?
    rw [Wrappers.next_function_with]
    exact program.commandExtension_body_with source main hIndex pool

theorem compile_body (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).funcs[source.funcs.length + (3 + index)]? =
      (program.functions source pool)[index]? := by
  layout_instance compile_body_with

theorem compile_body_type_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (callee : EffectVar effectSigs signature)
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).types[effectTypeIndex source callee.index]? =
      some signature.type := by
  cases main with
  | none =>
    change (Module.assembleWith calls source (Wrappers.extensionWith calls source
      (program.callableExtensionWith calls source entries pool))).types[
        effectTypeIndex source callee.index]? = some signature.type
    rw [Wrappers.next_type_with _ _ _ (by
      simp only [EffectProg.callableExtensionWith, List.length_append, EffectProg.types_length]
      have := callee.index_lt
      omega)]
    change (program.types ++ entries.map EffectEntry.type)[
      callee.index]? = some signature.type
    rw [List.getElem?_append_left (by rw [EffectProg.types_length]; exact callee.index_lt)]
    exact program.types_get callee
  | some main =>
    change (Module.assembleWith calls source (Wrappers.extensionWith calls source
      (program.commandExtensionWith calls source main pool))).types[
        effectTypeIndex source callee.index]? = some signature.type
    rw [Wrappers.next_type_with _ _ _ (by
      simp only [EffectProg.commandExtensionWith, List.length_append, EffectProg.types_length]
      have := callee.index_lt
      omega)]
    change (program.types ++ [startType])[callee.index]? = some signature.type
    rw [List.getElem?_append_left (by rw [EffectProg.types_length]; exact callee.index_lt)]
    exact program.types_get callee

theorem compile_body_type (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (callee : EffectVar effectSigs signature)
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).types[effectTypeIndex source callee.index]? =
      some signature.type := by
  layout_instance compile_body_type_with

theorem compile_entry_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (index : Nat)
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries none pool).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      (entries[index]?).map (fun entry =>
        entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index))) := by
  change (Module.assembleWith calls source (Wrappers.extensionWith calls source
    (program.callableExtensionWith calls source entries pool))).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      (entries[index]?).map (fun entry =>
        entry.functionWith calls source (effectTypeIndex source (effectSigs.length + index)))
  rw [Wrappers.next_function_with]
  exact program.callableExtension_entry_with source entries index pool

theorem compile_entry (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (index : Nat)
    (pool : Bytes.LiteralPool) :
    (compile source program entries none pool).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      (entries[index]?).map (fun entry =>
        entry.function source (effectTypeIndex source (effectSigs.length + index))) := by
  layout_instance compile_entry_with

theorem compile_start_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries (some main) pool).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (main.functionWith calls source (effectTypeIndex source effectSigs.length)) := by
  change (Module.assembleWith calls source (Wrappers.extensionWith calls source
    (program.commandExtensionWith calls source main pool))).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (main.functionWith calls source (effectTypeIndex source effectSigs.length))
  rw [Wrappers.next_function_with]
  exact program.commandExtension_start_with source main pool

theorem compile_start (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (compile source program entries (some main) pool).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (main.function source (effectTypeIndex source effectSigs.length)) := by
  layout_instance compile_start_with

@[simp] theorem compile_imports_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).imports = ABI.importsWith calls := rfl

@[simp] theorem compile_imports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).imports = ABI.imports := by
  layout_instance compile_imports_with

@[simp] theorem compile_memory_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).memory = source.memory := rfl

@[simp] theorem compile_memory (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).memory = source.memory := by
  layout_instance compile_memory_with

@[simp] theorem compile_globals_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).globals = source.globals := rfl

@[simp] theorem compile_globals (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).globals = source.globals := by
  layout_instance compile_globals_with

@[simp] theorem compile_memory64_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).memIs64 = source.memIs64 := rfl

@[simp] theorem compile_memory64 (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).memIs64 = source.memIs64 := by
  layout_instance compile_memory64_with

@[simp] theorem compile_memoryCap_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).memoryCap = source.memoryCap := rfl

@[simp] theorem compile_memoryCap (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).memoryCap = source.memoryCap := by
  layout_instance compile_memoryCap_with

@[simp] theorem compile_tableExports_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries main pool).tableExports = ABI.tableExports := rfl

@[simp] theorem compile_tableExports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).tableExports = ABI.tableExports := by
  layout_instance compile_tableExports_with

theorem compile_callable_exports_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries none pool).exports =
      [{ name := "alloc", funcIdx := Module.pureIndexWith calls 0 },
        { name := "release", funcIdx := Module.pureIndexWith calls 1 }] ++
      (entries.mapIdx fun index entry =>
        { name := entry.signature.name, funcIdx := Wrappers.effectIndexWith calls source (effectSigs.length + index) }) := by
  simp only [compileCalls, EffectProg.callableExtensionWith, List.mapIdx_eq_zipIdx_map, List.map_map,
    Function.comp_def]

theorem compile_callable_exports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries none pool).exports =
      [{ name := "alloc", funcIdx := Module.pureIndex 0 },
        { name := "release", funcIdx := Module.pureIndex 1 }] ++
      (entries.mapIdx fun index entry =>
        { name := entry.signature.name, funcIdx := Wrappers.effectIndex source (effectSigs.length + index) }) := by
  layout_instance compile_callable_exports_with

theorem compile_command_exports_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries (some main) pool).exports =
      [{ name := "_start", funcIdx := Wrappers.effectIndexWith calls source effectSigs.length }] := rfl

theorem compile_command_exports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    (compile source program entries (some main) pool).exports =
      [{ name := "_start", funcIdx := Wrappers.effectIndex source effectSigs.length }] := by
  layout_instance compile_command_exports_with

theorem compile_callable_counters_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries none pool).globalExports = source.globalExports := rfl

theorem compile_callable_counters (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries none pool).globalExports = source.globalExports := by
  layout_instance compile_callable_counters_with

theorem compile_command_counters_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    (compileCalls calls source program entries (some main) pool).globalExports = [] := rfl

theorem compile_command_counters (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    (compile source program entries (some main) pool).globalExports = [] := by
  layout_instance compile_command_counters_with

end Verified.Wasi
