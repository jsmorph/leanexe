import LeanExe.Runtime.Defs
import Verified.Tree

namespace Verified

open Wasm

/-- The first slot of a record's fields: 1 when slot 0 holds the tag. -/
def TreeShape.fieldStart (shape : TreeShape) : Nat := if shape.tagged then 1 else 0

/-- Code that stores the tag of record constructor `r` into slot 0 of the record at local `ptr`
when the shape is tagged. -/
def TreeShape.tagStoreCode (shape : TreeShape) (r : Fin shape.records) (ptr : Nat) : Program :=
  if shape.tagged then
    [.localGet ptr, .wrapI64, .constI64 (UInt64.ofNat (shape.ctorIndex r)), .store64 0]
  else []

def treeStoreFields (ptr : Nat) : Nat → Nat → Nat → List Bool → Program
  | _, _, _, [] => []
  | words, children, i, false :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .localGet words, .store64 0] ++ treeStoreFields ptr (words + 1) children (i + 1) rest
  | words, children, i, true :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .localGet children, .store64 0] ++ treeStoreFields ptr words (children + 1) (i + 1) rest

def treeLoadFields (ptr : Nat) : Nat → Nat → Nat → List Bool → Program
  | _, _, _, [] => []
  | words, children, i, false :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .load64 0, .localSet words] ++ treeLoadFields ptr (words + 1) children (i + 1) rest
  | words, children, i, true :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .load64 0, .localSet children] ++ treeLoadFields ptr words (children + 1) (i + 1) rest

def treeFieldLocs : List Bool → Nat → Nat → List Nat
  | [], _, _ => []
  | false :: rest, words, children => words :: treeFieldLocs rest (words + 1) children
  | true :: rest, words, children => children :: treeFieldLocs rest words (children + 1)

def recordStoreCode (ptr : Nat) : Nat → List Nat → Program
  | _, [] => []
  | i, src :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .localGet src, .store64 0] ++ recordStoreCode ptr (i + 1) rest

def recordLoadCode (ptr : Nat) : Nat → List Nat → Program
  | _, [] => []
  | i, dst :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .load64 0, .localSet dst] ++ recordLoadCode ptr (i + 1) rest

theorem treeStoreFields_eq (ptr words children i : Nat) (fields : List Bool) :
    treeStoreFields ptr words children i fields =
      recordStoreCode ptr i (treeFieldLocs fields words children) := by
  induction fields generalizing words children i with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [treeStoreFields, treeFieldLocs, recordStoreCode, ih]

theorem treeLoadFields_eq (ptr words children i : Nat) (fields : List Bool) :
    treeLoadFields ptr words children i fields =
      recordLoadCode ptr i (treeFieldLocs fields words children) := by
  induction fields generalizing words children i with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [treeLoadFields, treeFieldLocs, recordLoadCode, ih]

end Verified
