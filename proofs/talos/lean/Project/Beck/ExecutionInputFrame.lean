import Project.Beck.ExecutionJobs

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def inputInBounds : Wasm.Program :=
  match (func6[7]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def inputEligible : Wasm.Program :=
  match (inputInBounds[20]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

abbrev InputSaved := Fin 50 → Value
abbrev InputTail := Fin 10 → UInt64

def inputPrefix (saved : InputSaved) : List Value :=
  [saved 0, saved 1, saved 2, saved 3, saved 4, saved 5, saved 6, saved 7, saved 8, saved 9, saved 10, saved 11, saved 12, saved 13, saved 14, saved 15, saved 16, saved 17, saved 18, saved 19, saved 20, saved 21, saved 22, saved 23, saved 24, saved 25, saved 26, saved 27, saved 28, saved 29, saved 30, saved 31, saved 32, saved 33, saved 34, saved 35, saved 36, saved 37, saved 38, saved 39, saved 40, saved 41, saved 42, saved 43, saved 44, saved 45, saved 46, saved 47, saved 48, saved 49]

def inputFrame (pointer : UInt64) (saved : InputSaved) (tail : InputTail) : Locals :=
  { params := [.i64 pointer, .i64 pointer]
    locals := inputPrefix saved ++
      [.i64 (tail 0), .i64 (tail 1), .i64 (tail 2), .i64 (tail 3), .i64 (tail 4),
        .i64 (tail 5), .i64 (tail 6), .i64 (tail 7), .i64 (tail 8), .i64 (tail 9)] }

def inputEmptySaved (saved : InputSaved) (destination : Nat) (root : UInt64) (index : Fin 50) : Value :=
  if index.val = 20 ∨ index.val + 2 = destination then .i64 root else saved index

def inputEmptyTail (tail : InputTail) (root previous current capacity next : UInt64) (index : Fin 10) : UInt64 :=
  match index.val with
  | 0 | 9 => root
  | 4 => 8
  | 5 => previous
  | 6 => current
  | 7 => capacity
  | 8 => next
  | _ => tail index

def inputEmptyProgram (destination : Nat) : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 56 ++ FixedArrayAllocate.program 56 1 ++
    [.localGet 61, .localSet 52] ++ FixedArrayResult.lengthStoreProgram 52 0 ++
    [.localGet 52, .localSet 22, .localGet 22, .localSet destination]

set_option maxRecDepth 2048 in
theorem input_empty_shapes :
    (inputEligible.drop 34).take 43 = inputEmptyProgram 25 ∧
    (inputEligible.drop 77).take 43 = inputEmptyProgram 26 := ⟨rfl, rfl⟩

end Project.Beck.Execution
