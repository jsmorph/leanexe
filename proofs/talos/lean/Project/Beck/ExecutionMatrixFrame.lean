import Project.Beck.ExecutionMatrixCapacity
import Project.Beck.ExecutionCountStep

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

abbrev MatrixTail := Fin 15 → UInt64

def matrixParams (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) : List Value :=
  (inputValues input inputOwner inputPointer).reverse ++ (pointValues point pointOwner pointPointer).reverse

def matrixRowSaved (input : Input) (category index : Nat) (pointer : UInt64) (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 5 => .i64 category.toUInt64
  | 18 | 19 => .i64 pointer
  | 60 => .i64 index.toUInt64
  | 61 => .i64 input.jobs.toUInt64
  | 62 => .i64 1
  | _ => saved k

def matrixRowStable (before after : MatrixSaved) : Prop :=
  ∀ k, (k.val < 18 ∧ k.val ≠ 5 ∨ 33 ≤ k.val ∧ k.val < 60) → after k = before k

theorem matrixRowStable.refl (saved : MatrixSaved) : matrixRowStable saved saved := fun _ _ => rfl

theorem matrixRowStable.trans {a b c : MatrixSaved} (ab : matrixRowStable a b) (bc : matrixRowStable b c) :
    matrixRowStable a c := fun k hk => (bc k hk).trans (ab k hk)

def matrixRowAfter (owner : UInt64) (after : MatrixAfter) (k : Fin 9) : Value :=
  if k.val = 4 then .i64 owner else after k

def matrixTail (tail : MatrixTail) : List Value :=
  [.i64 (tail 0), .i64 (tail 1), .i64 (tail 2), .i64 (tail 3), .i64 (tail 4),
    .i64 (tail 5), .i64 (tail 6), .i64 (tail 7), .i64 (tail 8), .i64 (tail 9),
    .i64 (tail 10), .i64 (tail 11), .i64 (tail 12), .i64 (tail 13), .i64 (tail 14)]

def matrixRowFrame (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category index : Nat) (pointer initialOwner : UInt64) (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) : Locals :=
  { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
    locals := matrixPrefix (matrixRowSaved input category index pointer saved) ++ matrixTail tail ++
      matrixSuffix (matrixRowAfter initialOwner after) }

def matrixReadSaved (input : Input) (point : Point) (pointOwner pointPointer : UInt64)
    (category index : Nat) (pointer : UInt64) (saved : MatrixSaved) (k : Fin 63) : Value :=
  match k.val with
  | 20 | 26 => .i64 index.toUInt64
  | 22 | 27 => .i64 pointer
  | 23 => .i64 point.denominator
  | 24 => .i64 pointOwner
  | 25 => .i64 pointPointer
  | _ => matrixRowSaved input category index pointer saved k

def matrixEntryScratch (inputPointer : UInt64) (categories category index : Nat) (isFrozen : Bool)
    (tail : MatrixTail) (k : Fin 15) : UInt64 :=
  if isFrozen then tail k else
    match k.val with
    | 9 => inputPointer
    | 10 | 13 => (index * categories + category).toUInt64
    | 11 => (index * categories).toUInt64
    | 12 => category.toUInt64
    | 14 => index.toUInt64
    | _ => tail k

def matrixEntryAfter (input : Input) (initialOwner : UInt64) (isFrozen : Bool) (after : MatrixAfter) (k : Fin 9) : Value :=
  if !isFrozen && k.val = 0 then .i64 input.categories.toUInt64 else matrixRowAfter initialOwner after k

def matrixEntry (input : Input) (point : Point) (category index : Nat) : UInt64 :=
  if !frozen point index then input.incidence[index * input.categories + category]! else 0

end Project.Beck.Execution
