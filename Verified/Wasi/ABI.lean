import Interpreter.Wasm.Syntax

namespace Verified.Wasi.ABI

open Wasm

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

end Verified.Wasi.ABI
