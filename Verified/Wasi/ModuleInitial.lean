import Verified.Wasi.Module

namespace Verified.Wasi.Module

open Wasm

def initialStore (source : Wasm.Module) (extra : Extension) (world : World) : Store World :=
  PureTransport.restore world ((assemble source extra).initialStore : Store Unit)

@[simp] theorem initialStore_host (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).host = world := rfl

@[simp] theorem initialStore_mem (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).mem = (source.initialStore : Store Unit).mem := rfl

@[simp] theorem initialStore_globals (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).globals = (source.initialStore : Store Unit).globals := rfl

@[simp] theorem initialStore_memoryCaps (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).memoryCaps =
      (source.initialStore : Store Unit).memoryCaps := rfl

@[simp] theorem initialStore_dataSegments (source : Wasm.Module) (extra : Extension)
    (world : World) :
    (initialStore source extra world).dataSegments =
      (source.initialStore : Store Unit).dataSegments := rfl

@[simp] theorem initialStore_extraMems (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).extraMems = (source.initialStore : Store Unit).extraMems := rfl

@[simp] theorem initialStore_memoryCap (source : Wasm.Module) (extra : Extension)
    (world : World) :
    (initialStore source extra world).memoryCap (assemble source extra) 0 =
      (source.initialStore : Store Unit).memoryCap source 0 := rfl

theorem initialStore_functionIds (source : Wasm.Module) (extra : Extension) (world : World) :
    (initialStore source extra world).functionIds =
      List.range (3 + source.funcs.length + extra.funcs.length) := by
  change List.range (ABI.imports.length +
    (source.funcs.map Relocation.function ++ extra.funcs).length) = _
  simp only [ABI.imports_length, List.length_append, List.length_map, Nat.add_assoc]

theorem initialStore_tables (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    (initialStore source extra world).tables = [[]] := by
  simp only [initialStore, assemble, Wasm.Module.initialStore, PureTransport.restore,
    Store.mapHost, hElements, List.foldl_nil, ABI.functionTable,
    List.map_cons, List.map_nil, List.replicate_zero]

theorem initialStore_tableIds (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    (initialStore source extra world).tableIds = [0] := by
  change List.range (initialStore source extra world).tables.length = [0]
  rw [initialStore_tables source extra world hElements]
  rfl

theorem initialStore_eq (source : Wasm.Module) (extra : Extension) (world : World)
    (hElements : source.elements = []) :
    initialStore source extra world =
      { PureTransport.restore world (source.initialStore : Store Unit) with
        functionIds := List.range (3 + source.funcs.length + extra.funcs.length)
        tables := [[]]
        tableIds := [0] } := by
  simp only [initialStore, assemble, Wasm.Module.initialStore, PureTransport.restore,
    Store.mapHost, hElements, List.foldl_nil, ABI.functionTable, ABI.imports_length,
    List.map_cons, List.map_nil, List.replicate_zero, List.length_append,
    List.length_map, List.length_cons, List.length_nil, Nat.add_assoc] <;> rfl

end Verified.Wasi.Module
