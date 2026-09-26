import Project.Compiler.PayloadVectors
import Project.Compiler.MetadataParsing

namespace Project.Compiler.ArithmeticModule

open Project.Compiler.Parsing
open Wasm.Binary

abbrev B := LeanExe.Wasm.Binary.u32leb

def memoryItems : List (List UInt8) := [[0] ++ B 16]
def memoryPayload : List UInt8 := LeanExe.Wasm.Binary.vec memoryItems
def memoryValues : List MemoryType := [{ limits := { min := 16, max := none } }]

theorem memory_parsed : Parses (Wasm.Binary.vector memoryType) memoryPayload memoryValues := by
  apply encoded_vector (.cons (memory_min 16 (by decide)) .nil)
  · intro bs member
    simp only [memoryItems, List.mem_cons, List.not_mem_nil, or_false] at member
    subst bs
    simp
  · decide

def globalBytes (n : Nat) : List UInt8 :=
  LeanExe.Wasm.Binary.ofNats [126, 1] ++ LeanExe.Wasm.Binary.i64Const n ++ [11]
def globalValue (n : Nat) : Global :=
  { type := { type := .i64, mutability := .mutable }
    init := .i64Const (UInt64.ofNat n).toBitVec.toInt }
def globalItems : List (List UInt8) :=
  [globalBytes 4096, globalBytes 0, globalBytes 0, globalBytes 0, globalBytes 0, globalBytes 0]
def globalPayload : List UInt8 := LeanExe.Wasm.Binary.vec globalItems
def globalValues : List Global :=
  [globalValue 4096, globalValue 0, globalValue 0, globalValue 0, globalValue 0, globalValue 0]

theorem global_zero : Parses global (globalBytes 0) (globalValue 0) := by
  simpa [globalBytes, globalValue, LeanExe.Wasm.Binary.i64Const,
    LeanExe.Wasm.Binary.s64lebInt, LeanExe.Wasm.Binary.intBits,
    LeanExe.Wasm.Binary.ofNats, LeanExe.Wasm.Binary.byte, List.map_cons, List.map_nil,
    List.append_assoc] using global_i64 0

theorem global_initial : Parses global (globalBytes 4096) (globalValue 4096) := by
  simpa [globalBytes, globalValue, LeanExe.Wasm.Binary.i64Const,
    LeanExe.Wasm.Binary.s64lebInt, LeanExe.Wasm.Binary.intBits,
    LeanExe.Wasm.Binary.ofNats, LeanExe.Wasm.Binary.byte, List.map_cons, List.map_nil,
    List.append_assoc] using global_i64 4096

theorem globals_parsed : Parses (Wasm.Binary.vector global) globalPayload globalValues := by
  apply encoded_vector (.cons global_initial (.cons global_zero (.cons global_zero
    (.cons global_zero (.cons global_zero (.cons global_zero .nil))))))
  · intro bs member
    simp only [globalItems, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [globalBytes, LeanExe.Wasm.Binary.ofNats]
  · decide

def functionPayload : List UInt8 := LeanExe.Wasm.Binary.u32Vec (List.range 5)
def functionValues : List UInt32 := (List.range 5).map UInt32.ofNat

theorem functions_parsed : Parses (Wasm.Binary.vector Leb.u32) functionPayload functionValues := by
  apply unsigned_vector
  · intro n hn
    simp only [List.mem_range] at hn
    omega
  · decide

theorem memory_section : LeanExe.Wasm.Binary.CoreWasm.coreMemorySection =
    LeanExe.Wasm.Binary.wasmSection 5 memoryPayload := rfl

theorem global_section : LeanExe.Wasm.Binary.CoreWasm.coreGlobalSection =
    LeanExe.Wasm.Binary.wasmSection 6 globalPayload := rfl

theorem function_section (func : LeanExe.IR.Func) :
    LeanExe.Wasm.Binary.CoreWasm.functionSection { funcs := #[func] } =
      LeanExe.Wasm.Binary.wasmSection 3 functionPayload := rfl

end Project.Compiler.ArithmeticModule
