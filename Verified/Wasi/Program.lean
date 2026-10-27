import Verified.Wasi.ProgramIndex

namespace Verified.Wasi

open Wasm

def EffectProg.callableExtension (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) : Module.Extension :=
  { types := program.types ++ entries.map EffectEntry.type
    funcs := program.functions source pool ++ entries.mapIdx (fun index entry =>
      entry.function source (effectTypeIndex source (effectSigs.length + index)))
    exports := entries.mapIdx fun index entry =>
      { name := entry.signature.name, funcIdx := effectSigs.length + index } }

def EffectProg.commandExtension (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) : Module.Extension :=
  { types := program.types ++ [startType]
    funcs := program.functions source pool ++
      [main.function source (effectTypeIndex source effectSigs.length)]
    exports := [{ name := "_start", funcIdx := effectSigs.length }] }

def compile (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs) := none)
    (pool : Bytes.LiteralPool) : Wasm.Module :=
  let next := match main with
    | none => program.callableExtension source entries pool
    | some entry => program.commandExtension source entry pool
  let assembled := Module.assemble source (Wrappers.extension source next)
  { assembled with
    exports := (match main with
      | none => [{ name := "alloc", funcIdx := Module.pureIndex 0 },
          { name := "release", funcIdx := Module.pureIndex 1 }]
      | some _ => []) ++
      next.exports.map (fun entry => { entry with funcIdx := Wrappers.effectIndex source entry.funcIdx })
    globalExports := match main with
      | none => source.globalExports
      | some _ => []
    memoryExports := [("memory", 0)] }

theorem EffectProg.callableExtension_types_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).types.length =
      effectSigs.length + entries.length := by
  simp only [EffectProg.callableExtension, List.length_append, List.length_map,
    EffectProg.types_length]

theorem EffectProg.callableExtension_funcs_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).funcs.length =
      effectSigs.length + entries.length := by
  simp only [EffectProg.callableExtension, List.length_append, List.length_mapIdx,
    program.functions_length source pool]

theorem EffectProg.commandExtension_types_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).types.length = effectSigs.length + 1 := by
  simp only [EffectProg.commandExtension, List.length_append, List.length_cons, List.length_nil,
    EffectProg.types_length]

theorem EffectProg.commandExtension_funcs_length (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).funcs.length = effectSigs.length + 1 := by
  simp only [EffectProg.commandExtension, List.length_append, List.length_cons, List.length_nil,
    program.functions_length source pool]

theorem EffectProg.callableExtension_body (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).funcs[index]? =
      (program.functions source pool)[index]? := by
  exact List.getElem?_append_left (by rw [program.functions_length source pool]; exact hIndex)

theorem EffectProg.callableExtension_entry (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (index : Nat) (pool : Bytes.LiteralPool) :
    (program.callableExtension source entries pool).funcs[effectSigs.length + index]? =
      (entries[index]?).map (fun entry =>
        entry.function source (effectTypeIndex source (effectSigs.length + index))) := by
  rw [EffectProg.callableExtension,
    List.getElem?_append_right (by rw [program.functions_length source pool]; omega),
    program.functions_length source pool, Nat.add_sub_cancel_left, List.getElem?_mapIdx]

theorem EffectProg.commandExtension_body (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).funcs[index]? =
      (program.functions source pool)[index]? := by
  exact List.getElem?_append_left (by rw [program.functions_length source pool]; exact hIndex)

theorem EffectProg.commandExtension_start (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (program.commandExtension source main pool).funcs[effectSigs.length]? =
      some (main.function source (effectTypeIndex source effectSigs.length)) := by
  rw [EffectProg.commandExtension,
    List.getElem?_append_right (by rw [program.functions_length source pool]),
    program.functions_length source pool, Nat.sub_self]
  rfl

theorem Wrappers.next_type (source : Wasm.Module) (next : Module.Extension) (index : Nat) :
    (Module.assemble source (Wrappers.extension source next)).types[
      effectTypeIndex source index]? = next.types[index]? := by
  rw [effectTypeIndex, Module.extra_type_index]
  change (Wrappers.readType :: Wrappers.writeType :: next.types)[2 + index]? = _
  rw [Nat.add_comm 2 index]
  rfl

theorem compile_body (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    {index : Nat} (hIndex : index < effectSigs.length)
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).funcs[source.funcs.length + (3 + index)]? =
      (program.functions source pool)[index]? := by
  cases main with
  | none =>
    change (Module.assemble source (Wrappers.extension source
      (program.callableExtension source entries pool))).funcs[
        source.funcs.length + (3 + index)]? = (program.functions source pool)[index]?
    rw [Wrappers.next_function]
    exact program.callableExtension_body source entries hIndex pool
  | some main =>
    change (Module.assemble source (Wrappers.extension source
      (program.commandExtension source main pool))).funcs[
        source.funcs.length + (3 + index)]? = (program.functions source pool)[index]?
    rw [Wrappers.next_function]
    exact program.commandExtension_body source main hIndex pool

theorem compile_body_type (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : Option (EffectMain effectSigs))
    (callee : EffectVar effectSigs signature)
    (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).types[effectTypeIndex source callee.index]? =
      some signature.type := by
  cases main with
  | none =>
    change (Module.assemble source (Wrappers.extension source
      (program.callableExtension source entries pool))).types[
        effectTypeIndex source callee.index]? = some signature.type
    rw [Wrappers.next_type]
    change (program.types ++ entries.map EffectEntry.type)[
      callee.index]? = some signature.type
    rw [List.getElem?_append_left (by rw [EffectProg.types_length]; exact callee.index_lt)]
    exact program.types_get callee
  | some main =>
    change (Module.assemble source (Wrappers.extension source
      (program.commandExtension source main pool))).types[
        effectTypeIndex source callee.index]? = some signature.type
    rw [Wrappers.next_type]
    change (program.types ++ [startType])[callee.index]? = some signature.type
    rw [List.getElem?_append_left (by rw [EffectProg.types_length]; exact callee.index_lt)]
    exact program.types_get callee

theorem compile_entry (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (index : Nat)
    (pool : Bytes.LiteralPool) :
    (compile source program entries none pool).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      (entries[index]?).map (fun entry =>
        entry.function source (effectTypeIndex source (effectSigs.length + index))) := by
  change (Module.assemble source (Wrappers.extension source
    (program.callableExtension source entries pool))).funcs[
      source.funcs.length + (3 + (effectSigs.length + index))]? =
      (entries[index]?).map (fun entry =>
        entry.function source (effectTypeIndex source (effectSigs.length + index)))
  rw [Wrappers.next_function]
  exact program.callableExtension_entry source entries index pool

theorem compile_start (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entries : List (EffectEntry effectSigs)) (main : EffectMain effectSigs)
    (pool : Bytes.LiteralPool) :
    (compile source program entries (some main) pool).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (main.function source (effectTypeIndex source effectSigs.length)) := by
  change (Module.assemble source (Wrappers.extension source
    (program.commandExtension source main pool))).funcs[
      source.funcs.length + (3 + effectSigs.length)]? =
      some (main.function source (effectTypeIndex source effectSigs.length))
  rw [Wrappers.next_function]
  exact program.commandExtension_start source main pool

@[simp] theorem compile_imports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).imports = ABI.imports := rfl

@[simp] theorem compile_memory (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).memory = source.memory := rfl

@[simp] theorem compile_globals (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).globals = source.globals := rfl

@[simp] theorem compile_memory64 (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).memIs64 = source.memIs64 := rfl

@[simp] theorem compile_memoryCap (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).memoryCap = source.memoryCap := rfl

@[simp] theorem compile_tableExports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : Option (EffectMain effectSigs)) (pool : Bytes.LiteralPool) :
    (compile source program entries main pool).tableExports = ABI.tableExports := rfl

theorem compile_callable_exports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries none pool).exports =
      [{ name := "alloc", funcIdx := Module.pureIndex 0 },
        { name := "release", funcIdx := Module.pureIndex 1 }] ++
      (entries.mapIdx fun index entry =>
        { name := entry.signature.name, funcIdx := Wrappers.effectIndex source (effectSigs.length + index) }) := by
  simp only [compile, EffectProg.callableExtension, List.mapIdx_eq_zipIdx_map, List.map_map,
    Function.comp_def]

theorem compile_command_exports (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    (compile source program entries (some main) pool).exports =
      [{ name := "_start", funcIdx := Wrappers.effectIndex source effectSigs.length }] := rfl

theorem compile_callable_counters (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (pool : Bytes.LiteralPool) :
    (compile source program entries none pool).globalExports = source.globalExports := rfl

theorem compile_command_counters (source : Wasm.Module)
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool) :
    (compile source program entries (some main) pool).globalExports = [] := rfl

end Verified.Wasi
