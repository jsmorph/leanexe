import Project.Beck.ExecutionBorderCapacity
import Project.Beck.ExecutionContains

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

abbrev BorderTail := Fin 15 → UInt64

def borderParams (width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat) : List Value :=
  [.i64 width.toUInt64, .i64 matrixOwner, .i64 matrixPointer] ++
    (basisValues basis rowOwner rowPointer columnOwner columnPointer).reverse ++ [.i64 row.toUInt64, .i64 column.toUInt64]

def borderTail (tail : BorderTail) : List Value :=
  [.i64 (tail 0), .i64 (tail 1), .i64 (tail 2), .i64 (tail 3), .i64 (tail 4), .i64 (tail 5), .i64 (tail 6), .i64 (tail 7), .i64 (tail 8), .i64 (tail 9), .i64 (tail 10), .i64 (tail 11), .i64 (tail 12), .i64 (tail 13), .i64 (tail 14)]

def borderFrame (params : List Value) (saved : BorderSaved) (tail : BorderTail) : Locals :=
  { params := params, locals := borderPrefix saved ++ borderTail tail }

def borderPreparedSaved (saved : BorderSaved) (columns : Bool) (pointer : UInt64) (k : Fin 30) : Value :=
  if k.val = (if columns then 10 else 6) then .i64 pointer else saved k

def borderInstalledSaved (saved : BorderSaved) (columns : Bool) (root : UInt64) (k : Fin 30) : Value :=
  if k.val = (if columns then 12 else 8) ∨ k.val = (if columns then 13 else 9) then .i64 root else saved k

end Project.Beck.Execution
