import Project.Compiler.HeaderParsing

namespace Project.Compiler.Parsing

open Wasm.Binary

inductive ExportKind where
  | func | memory | global

def ExportKind.tag : ExportKind → Nat
  | .func => 0
  | .memory => 2
  | .global => 3

def ExportKind.desc (kind : ExportKind) (index : Nat) : ExportDesc :=
  match kind with
  | .func => .func (UInt32.ofNat index)
  | .memory => .memory (UInt32.ofNat index)
  | .global => .global (UInt32.ofNat index)

theorem export_desc (kind : ExportKind) (index : Nat) (bound : index < 2 ^ 32) :
    Parses exportDesc ([UInt8.ofNat kind.tag] ++ LeanExe.Wasm.Binary.u32leb index)
      (kind.desc index) := by
  cases kind <;> unfold exportDesc
  · apply bind_parses (a := [0]) (read_byte 0)
    exact map_parses (u32 index bound) ExportDesc.func
  · apply bind_parses (a := [2]) (read_byte 2)
    exact map_parses (u32 index bound) ExportDesc.memory
  · apply bind_parses (a := [3]) (read_byte 3)
    exact map_parses (u32 index bound) ExportDesc.global

theorem export_entry (text : String) (kind : ExportKind) (index : Nat)
    (nameBound : text.toUTF8.size < 2 ^ 32) (indexBound : index < 2 ^ 32) :
    Parses exportEntry (LeanExe.Wasm.Binary.exportEntry text kind.tag index)
      { name := { bytes := text.toUTF8.data.toList, text }, desc := kind.desc index } := by
  unfold exportEntry LeanExe.Wasm.Binary.exportEntry
  simpa only [LeanExe.Wasm.Binary.ofNats, List.map_cons, List.map_nil,
    LeanExe.Wasm.Binary.byte, List.append_assoc] using
    bind_parses (q := fun parsedName => do
      let desc ← exportDesc
      pure ({ name := parsedName, desc } : Export)) (name text nameBound)
      (map_parses (export_desc kind index indexBound) (fun desc =>
        ({ name := { bytes := text.toUTF8.data.toList, text }, desc } : Export)))

theorem limits_min (pages : Nat) (bound : pages < 2 ^ 32) :
    Parses limits ([0] ++ LeanExe.Wasm.Binary.u32leb pages)
      { min := UInt32.ofNat pages, max := none } := by
  unfold limits
  apply bind_parses (read_byte 0)
  exact map_parses (u32 pages bound) (fun min => ({ min, max := none } : Limits))

theorem memory_min (pages : Nat) (bound : pages < 2 ^ 32) :
    Parses memoryType ([0] ++ LeanExe.Wasm.Binary.u32leb pages)
      { limits := { min := UInt32.ofNat pages, max := none } } := by
  exact map_parses (limits_min pages bound) (fun limits => ({ limits } : MemoryType))

theorem mutable : Parses mutability [1] .mutable := by
  unfold mutability
  apply bind_parses (a := [1]) (b := []) (read_byte 1)
  exact pure_parses _

theorem global_type : Parses globalType [126, 1] { type := .i64, mutability := .mutable } := by
  unfold globalType
  exact bind_parses val_i64 (map_parses mutable
    (fun mutability => ({ type := .i64, mutability } : GlobalType)))

theorem const_expression (value : UInt64) :
    Parses constExpr ([66] ++ ((LeanExe.Wasm.Leb.s64lebU64 value).toList ++ [11]))
      (.i64Const value.toBitVec.toInt) := by
  unfold constExpr
  apply bind_parses (read_byte 66)
  apply bind_parses (s64 value)
  exact map_parses (expect_byte 11) (fun _ => ConstExpr.i64Const value.toBitVec.toInt)

theorem global_i64 (value : UInt64) :
    Parses global ([126, 1] ++ ([66] ++ ((LeanExe.Wasm.Leb.s64lebU64 value).toList ++ [11])))
      { type := { type := .i64, mutability := .mutable }, init := .i64Const value.toBitVec.toInt } := by
  unfold global
  exact bind_parses global_type (map_parses (const_expression value)
    (fun init => ({ type := { type := .i64, mutability := .mutable }, init } : Global)))

end Project.Compiler.Parsing
