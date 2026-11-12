import Verified.Wasi.Module

namespace Verified.Wasi.Module

open Wasm

def initialStoreWith (calls : List LeanExe.Wasi.Call) (source : Wasm.Module) (extra : Extension) (world : World) : Store World :=
  PureTransport.restore world ((assembleWith calls source extra).initialStore : Store Unit)

def initialStore (source : Wasm.Module) (extra : Extension) (world : World) : Store World :=
  initialStoreWith [] source extra world

@[simp] theorem initialStore_host_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStoreWith calls source extra world).host = world := rfl

@[simp] theorem initialStore_host (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).host = world := by
  layout_instance initialStore_host_with

@[simp] theorem initialStore_mem_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStoreWith calls source extra world).mem = (source.initialStore : Store Unit).mem := rfl

@[simp] theorem initialStore_mem (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).mem = (source.initialStore : Store Unit).mem := by
  layout_instance initialStore_mem_with

@[simp] theorem initialStore_globals_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStoreWith calls source extra world).globals = (source.initialStore : Store Unit).globals := rfl

@[simp] theorem initialStore_globals (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).globals = (source.initialStore : Store Unit).globals := by
  layout_instance initialStore_globals_with

@[simp] theorem initialStore_memoryCaps_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStoreWith calls source extra world).memoryCaps =
      (source.initialStore : Store Unit).memoryCaps := rfl

@[simp] theorem initialStore_memoryCaps (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).memoryCaps =
      (source.initialStore : Store Unit).memoryCaps := by
  layout_instance initialStore_memoryCaps_with

@[simp] theorem initialStore_dataSegments_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension)
    (world : World) :
    (initialStoreWith calls source extra world).dataSegments =
      (source.initialStore : Store Unit).dataSegments := rfl

@[simp] theorem initialStore_dataSegments (source : Wasm.Module) (extra : Extension)
    (world : World) :
    (initialStore source extra world).dataSegments =
      (source.initialStore : Store Unit).dataSegments := by
  layout_instance initialStore_dataSegments_with

@[simp] theorem initialStore_extraMems_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStoreWith calls source extra world).extraMems = (source.initialStore : Store Unit).extraMems := rfl

@[simp] theorem initialStore_extraMems (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).extraMems = (source.initialStore : Store Unit).extraMems := by
  layout_instance initialStore_extraMems_with

@[simp] theorem initialStore_memoryCap_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension)
    (world : World) :
    (initialStoreWith calls source extra world).memoryCap (assembleWith calls source extra) 0 =
      (source.initialStore : Store Unit).memoryCap source 0 := rfl

@[simp] theorem initialStore_memoryCap (source : Wasm.Module) (extra : Extension)
    (world : World) :
    (initialStore source extra world).memoryCap (assemble source extra) 0 =
      (source.initialStore : Store Unit).memoryCap source 0 := by
  layout_instance initialStore_memoryCap_with

theorem initialStore_functionIds_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStoreWith calls source extra world).functionIds =
      List.range ((3 + calls.length) + source.funcs.length + extra.funcs.length) := by
  change List.range ((ABI.importsWith calls).length +
    (source.funcs.map (Relocation.functionWith calls) ++ extra.funcs).length) = _
  simp only [ABI.importsWith_length, List.length_append, List.length_map, Nat.add_assoc]

theorem initialStore_functionIds (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).functionIds =
      List.range (3 + source.funcs.length + extra.funcs.length) := by
  layout_instance initialStore_functionIds_with

theorem initialStore_tables_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    (initialStoreWith calls source extra world).tables = [[]] := by
  simp only [initialStoreWith, assembleWith, Wasm.Module.initialStore, PureTransport.restore,
    Store.mapHost, hElements, List.foldl_nil, ABI.functionTable,
    List.map_cons, List.map_nil, List.replicate_zero]

theorem initialStore_tables (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    (initialStore source extra world).tables = [[]] := by
  layout_instance initialStore_tables_with

theorem initialStore_tableIds_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    (initialStoreWith calls source extra world).tableIds = [0] := by
  change List.range (initialStoreWith calls source extra world).tables.length = [0]
  rw [initialStore_tables_with source extra world hElements]
  rfl

theorem initialStore_tableIds (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    (initialStore source extra world).tableIds = [0] := by
  layout_instance initialStore_tableIds_with

theorem initialStore_eq_with {calls : List LeanExe.Wasi.Call}
    (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    initialStoreWith calls source extra world =
      { PureTransport.restore world (source.initialStore : Store Unit) with
        functionIds := List.range ((3 + calls.length) + source.funcs.length + extra.funcs.length)
        tables := [[]]
        tableIds := [0] } := by
  simp only [initialStoreWith, assembleWith, Wasm.Module.initialStore, PureTransport.restore,
    Store.mapHost, hElements, List.foldl_nil, ABI.functionTable, ABI.importsWith_length,
    List.map_cons, List.map_nil, List.replicate_zero, List.length_append,
    List.length_map, List.length_cons, List.length_nil, Nat.add_assoc] <;> rfl

theorem initialStore_eq (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    initialStore source extra world =
      { PureTransport.restore world (source.initialStore : Store Unit) with
        functionIds := List.range (3 + source.funcs.length + extra.funcs.length)
        tables := [[]]
        tableIds := [0] } := by
  layout_instance initialStore_eq_with

end Verified.Wasi.Module
