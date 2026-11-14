import Interpreter.Wasm.Syntax
import LeanExe.Wasi.Calls

namespace Verified.Wasi.ABI

open Wasm LeanExe.Wasi

def transferType : FuncType :=
  { params := [.i32, .i32, .i32, .i32], results := [.i32] }

def exitType : FuncType := { params := [.i32], results := [] }

def imports : List ImportDecl :=
  [{ «module» := "wasi_snapshot_preview1", name := "fd_read",
      params := transferType.params, results := transferType.results },
   { «module» := "wasi_snapshot_preview1", name := "fd_write",
      params := transferType.params, results := transferType.results },
   { «module» := "wasi_snapshot_preview1", name := "proc_exit",
      params := exitType.params, results := exitType.results }]

def types : List FuncType := [transferType, transferType, exitType]

def scratch : Nat × Nat := (0, 16)

def functionTable : TableDecl := { min := 0 }

def tableExports : List (String × Nat) := [("__indirect_function_table", 0)]

theorem imports_length : imports.length = 3 := rfl

theorem types_length : types.length = 3 := rfl

/-- The core types of a parameter's arguments: one `i32` for a 32-bit value, an enum, 32-bit flags,
a result, a reported region, or a record, one `i64` for a 64-bit value or 64-bit flags, and an
`i32` pointer and an `i32` length for an input or an output. -/
def paramTypes : Param → List ValueType
  | .word32 | .enum32 _ | .flags32 _ | .result32 | .result64 | .reported .. | .record .. => [.i32]
  | .word64 | .flags64 _ => [.i64]
  | .input | .output => [.i32, .i32]

/-- The core type of a flat call: its parameters' types and the errno. -/
def callType (call : Call) : FuncType :=
  { params := call.params.flatMap paramTypes, results := [.i32] }

def callImport (call : Call) : ImportDecl :=
  { «module» := "wasi_snapshot_preview1", name := call.name,
    params := (callType call).params, results := (callType call).results }

/-- The imports of a module whose program uses the flat calls `calls`: the three stream imports,
then one import for each call.  The empty list gives `imports` itself. -/
def importsWith : List Call → List ImportDecl
  | [] => imports
  | calls => imports ++ calls.map callImport

theorem importsWith_eq (calls : List Call) : importsWith calls = imports ++ calls.map callImport := by
  cases calls <;> rfl

theorem importsWith_length (calls : List Call) : (importsWith calls).length = 3 + calls.length := by
  simp only [importsWith_eq, List.length_append, List.length_map, imports_length]

theorem importsWith_nil : importsWith [] = imports := rfl

@[simp] theorem importsWith_getElem? (calls : List Call) {index : Nat} (h : index < 3) :
    (importsWith calls)[index]? = imports[index]? := by
  rw [importsWith_eq, List.getElem?_append_left (by rw [imports_length]; exact h)]

theorem importsWith_get (calls : List Call) {index : Nat} (h : index < 3) :
    (importsWith calls)[index]? = some imports[index]! := by
  rw [importsWith_getElem? calls h]
  match index, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- `types` followed by the types of the calls' imports.  The empty list gives `types` itself. -/
def withCallTypes (types : List FuncType) : List Call → List FuncType
  | [] => types
  | calls => types ++ calls.map callType

theorem withCallTypes_eq (types : List FuncType) (calls : List Call) :
    withCallTypes types calls = types ++ calls.map callType := by
  cases calls <;> simp [withCallTypes]

end Verified.Wasi.ABI
