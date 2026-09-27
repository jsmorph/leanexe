import Project.Beck.ExecutionMatrixRowLoop
import Project.Beck.ExecutionCount
import Project.ProofKit.CallRemainder

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixPlainFrame (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) : Locals :=
  { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
    locals := matrixPrefix saved ++ matrixTail tail ++ matrixSuffix after }

def matrixOuterSaved (input : Input) (category : Nat) (pointer owner : UInt64) (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 1 => .i64 owner
  | 3 | 4 => .i64 pointer
  | 57 => .i64 category.toUInt64
  | 58 => .i64 input.categories.toUInt64
  | 59 => .i64 1
  | _ => saved k

def matrixOuterFrame (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category : Nat) (pointer owner : UInt64) (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) : Locals :=
  matrixPlainFrame input point inputOwner inputPointer pointOwner pointPointer
    (matrixOuterSaved input category pointer owner saved) tail after

def matrixBranchSaved (input : Input) (category : Nat) (pointer owner : UInt64) (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 1 => .i64 owner
  | 5 | 57 => .i64 category.toUInt64
  | 37 | 38 => .i64 pointer
  | 58 => .i64 input.categories.toUInt64
  | 59 => .i64 1
  | _ => saved k

def matrixBranchFrame (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category : Nat) (pointer owner : UInt64) (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) : Locals :=
  matrixPlainFrame input point inputOwner inputPointer pointOwner pointPointer
    (matrixBranchSaved input category pointer owner saved) tail after

def matrixSelectedSaved (input : Input) (category : Nat) (pointer : UInt64) (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 33 | 34 | 35 | 36 | 37 | 38 => .i64 pointer
  | _ => matrixRowSaved input category input.jobs pointer saved k

end Project.Beck.Execution
