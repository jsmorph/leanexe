import Project.Compiler.FixedPayloads

namespace Project.Compiler.ArithmeticModule

open Project.Compiler.Parsing
open Wasm.Binary

def typeItems (func : LeanExe.IR.Func) : List (List UInt8) :=
  [LeanExe.Wasm.Binary.CoreWasm.typeForFunc func,
   LeanExe.Wasm.Binary.funcType [126] [126], LeanExe.Wasm.Binary.funcType [] [],
   LeanExe.Wasm.Binary.funcType [126] [126], LeanExe.Wasm.Binary.funcType [126] []]
def typePayload (func : LeanExe.IR.Func) : List UInt8 := LeanExe.Wasm.Binary.vec (typeItems func)
def typeValues (func : LeanExe.IR.Func) : List FuncType :=
  [{ params := List.replicate func.params .i64, results := List.replicate func.results.length .i64 },
   { params := [.i64], results := [.i64] }, { params := [], results := [] },
   { params := [.i64], results := [.i64] }, { params := [.i64], results := [] }]

theorem types_parsed (func : LeanExe.IR.Func)
    (pb : func.params < 2 ^ 32) (rb : func.results.length < 2 ^ 32) :
    Parses (Wasm.Binary.vector funcType) (typePayload func) (typeValues func) := by
  have userType : Parses funcType (LeanExe.Wasm.Binary.CoreWasm.typeForFunc func)
      { params := List.replicate func.params .i64, results := List.replicate func.results.length .i64 } := by
    exact function_type func.params func.results.length pb rb
  apply encoded_vector (.cons userType
    (.cons (function_type 1 1 (by decide) (by decide))
    (.cons (function_type 0 0 (by decide) (by decide))
    (.cons (function_type 1 1 (by decide) (by decide))
    (.cons (function_type 1 0 (by decide) (by decide)) .nil)))))
  · intro bs member
    simp only [typeItems, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [LeanExe.Wasm.Binary.CoreWasm.typeForFunc, LeanExe.Wasm.Binary.funcType]
  · change 5 < 2 ^ 32
    decide

def exportValue (text : String) (kind : ExportKind) (index : Nat) : Export :=
  { name := { bytes := text.toUTF8.data.toList, text }, desc := kind.desc index }

def exportItems (entry : String) : List (List UInt8) :=
  [LeanExe.Wasm.Binary.exportEntry "memory" 2 0,
   LeanExe.Wasm.Binary.exportEntry entry 0 0,
   LeanExe.Wasm.Binary.exportEntry "alloc" 0 1,
   LeanExe.Wasm.Binary.exportEntry "reset" 0 2,
   LeanExe.Wasm.Binary.exportEntry "retain" 0 3,
   LeanExe.Wasm.Binary.exportEntry "release" 0 4,
   LeanExe.Wasm.Binary.exportEntry "free" 0 4,
   LeanExe.Wasm.Binary.exportEntry "allocCount" 3 2,
   LeanExe.Wasm.Binary.exportEntry "retainCount" 3 3,
   LeanExe.Wasm.Binary.exportEntry "releaseCount" 3 4,
   LeanExe.Wasm.Binary.exportEntry "freeCount" 3 5]
def exportPayload (entry : String) : List UInt8 := LeanExe.Wasm.Binary.vec (exportItems entry)
def exportValues (entry : String) : List Export :=
  [exportValue "memory" .memory 0,
   exportValue entry .func 0,
   exportValue "alloc" .func 1,
   exportValue "reset" .func 2,
   exportValue "retain" .func 3,
   exportValue "release" .func 4,
   exportValue "free" .func 4,
   exportValue "allocCount" .global 2,
   exportValue "retainCount" .global 3,
   exportValue "releaseCount" .global 4,
   exportValue "freeCount" .global 5]

theorem exports_parsed (entry : String) (bound : entry.toUTF8.size < 2 ^ 32) :
    Parses (Wasm.Binary.vector exportEntry) (exportPayload entry) (exportValues entry) := by
  apply encoded_vector
    (.cons (export_entry "memory" .memory 0 (by decide) (by decide))
    (.cons (export_entry entry .func 0 bound (by decide))
    (.cons (export_entry "alloc" .func 1 (by decide) (by decide))
    (.cons (export_entry "reset" .func 2 (by decide) (by decide))
    (.cons (export_entry "retain" .func 3 (by decide) (by decide))
    (.cons (export_entry "release" .func 4 (by decide) (by decide))
    (.cons (export_entry "free" .func 4 (by decide) (by decide))
    (.cons (export_entry "allocCount" .global 2 (by decide) (by decide))
    (.cons (export_entry "retainCount" .global 3 (by decide) (by decide))
    (.cons (export_entry "releaseCount" .global 4 (by decide) (by decide))
    (.cons (export_entry "freeCount" .global 5 (by decide) (by decide))
    .nil)))))))))))
  · intro bs member
    simp only [exportItems, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [LeanExe.Wasm.Binary.exportEntry, LeanExe.Wasm.Binary.ofNats]
  · change 11 < 2 ^ 32
    decide

theorem type_section (func : LeanExe.IR.Func) :
    LeanExe.Wasm.Binary.CoreWasm.typeSection { funcs := #[func] } =
      LeanExe.Wasm.Binary.wasmSection 1 (typePayload func) := rfl

theorem export_section (func : LeanExe.IR.Func) (entry : String)
    (named : func.exportName = some entry) :
    LeanExe.Wasm.Binary.CoreWasm.exportSection { funcs := #[func] } =
      LeanExe.Wasm.Binary.wasmSection 7 (exportPayload entry) := by
  simp [LeanExe.Wasm.Binary.CoreWasm.exportSection, LeanExe.Wasm.Binary.CoreWasm.enumerate,
    LeanExe.Wasm.Binary.CoreWasm.enumerateAux,
    named, exportPayload, exportItems, LeanExe.Wasm.Binary.CoreWasm.runtimeStatGlobal]

end Project.Compiler.ArithmeticModule
