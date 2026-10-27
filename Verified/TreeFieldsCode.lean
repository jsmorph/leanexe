import LeanExe.Runtime.Defs
import Verified.Tree
import Verified.LocalFrame

namespace Verified

open Wasm

/-- The instructions that turn a word of type `ty` on top of the stack into the i64 that holds it
in an array: an f64 becomes an i64 bit pattern, and an f32 bit pattern is zero-extended to i64. -/
def toWordCode : ValueType → Program
  | .f64 => [.i64ReinterpretF64]
  | .f32 => [.i32ReinterpretF32, .extendUI32]
  | _ => []

/-- The instructions that turn the i64 that holds a word of type `ty` in an array into the
word. -/
def ofWordCode : ValueType → Program
  | .f64 => [.f64ReinterpretI64]
  | .f32 => [.wrapI64, .f32ReinterpretI32]
  | _ => []

/-- The WebAssembly type of an element of one word: i64 for a word or a `Bool`, and the float
types for floats. -/
def Elem.slotType : Elem → ValueType
  | .float => .f64
  | .float32 => .f32
  | _ => .i64

/-- The WebAssembly types of record constructor `r`'s word fields, in order. -/
def TreeShape.wordTypes (shape : TreeShape) (r : Fin shape.records) : List ValueType :=
  List.ofFn fun i => (shape.elem r i).slotType

/-- The first slot of a record's fields: 1 when slot 0 holds the tag. -/
def TreeShape.fieldStart (shape : TreeShape) : Nat := if shape.tagged then 1 else 0

/-- Code that stores the tag of record constructor `r` into slot 0 of the record at local `ptr`
when the shape is tagged. -/
def TreeShape.tagStoreCode (shape : TreeShape) (r : Fin shape.records) (ptr : Nat) : Program :=
  if shape.tagged then
    [.localGet ptr, .wrapI64, .constI64 (UInt64.ofNat (shape.ctorIndex r)), .store64 0]
  else []

/-- Code that stores the words from position `words` on, of the types `tys`, and the children from
local `children` on into the slots from `i` on of the record at local `ptr`, in the order of the
slot kinds `fields`, in a function of `h` positions. -/
def treeStoreFields (h ptr : Nat) : List ValueType → Nat → Nat → Nat → List Bool → Program
  | _, _, _, _, [] => []
  | tys, words, children, i, false :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .localGet (slotIndex h words (tys.headD .i64))] ++ toWordCode (tys.headD .i64) ++
      [.store64 0] ++ treeStoreFields h ptr tys.tail (words + 1) children (i + 1) rest
  | tys, words, children, i, true :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .localGet children, .store64 0] ++ treeStoreFields h ptr tys words (children + 1) (i + 1) rest

/-- Code that loads the slots from `i` on of the record at local `ptr` into the words from
position `words` on, of the types `tys`, and the children from local `children` on. -/
def treeLoadFields (h ptr : Nat) : List ValueType → Nat → Nat → Nat → List Bool → Program
  | _, _, _, _, [] => []
  | tys, words, children, i, false :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64, .load64 0] ++
      ofWordCode (tys.headD .i64) ++ [.localSet (slotIndex h words (tys.headD .i64))] ++
      treeLoadFields h ptr tys.tail (words + 1) children (i + 1) rest
  | tys, words, children, i, true :: rest =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .load64 0, .localSet children] ++ treeLoadFields h ptr tys words (children + 1) (i + 1) rest

def treeFieldLocs : List Bool → Nat → Nat → List Nat
  | [], _, _ => []
  | false :: rest, words, children => words :: treeFieldLocs rest (words + 1) children
  | true :: rest, words, children => children :: treeFieldLocs rest words (children + 1)

/-- The WebAssembly type of each slot, in the order of the slot kinds `fields`: the types `tys` of
the words in turn, and i64 for a child. -/
def treeFieldTypes : List Bool → List ValueType → List ValueType
  | [], _ => []
  | false :: rest, tys => tys.headD .i64 :: treeFieldTypes rest tys.tail
  | true :: rest, tys => .i64 :: treeFieldTypes rest tys

/-- Code that stores the values at positions `srcs`, of the types `tys`, into the slots from `i`
on of the record at local `ptr`, as i64 words. -/
def recordStoreCode (h ptr : Nat) : Nat → List Nat → List ValueType → Program
  | _, [], _ => []
  | i, src :: rest, tys =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64,
      .localGet (slotIndex h src (tys.headD .i64))] ++ toWordCode (tys.headD .i64) ++
      [.store64 0] ++ recordStoreCode h ptr (i + 1) rest tys.tail

/-- Code that loads the slots from `i` on of the record at local `ptr` into the positions `dsts`,
as values of the types `tys`. -/
def recordLoadCode (h ptr : Nat) : Nat → List Nat → List ValueType → Program
  | _, [], _ => []
  | i, dst :: rest, tys =>
    [.localGet ptr, .constI64 (UInt64.ofNat (8 * i)), .addI64, .wrapI64, .load64 0] ++
      ofWordCode (tys.headD .i64) ++ [.localSet (slotIndex h dst (tys.headD .i64))] ++
      recordLoadCode h ptr (i + 1) rest tys.tail

theorem treeStoreFields_eq (h ptr : Nat) (tys : List ValueType) (words children i : Nat)
    (fields : List Bool) :
    treeStoreFields h ptr tys words children i fields =
      recordStoreCode h ptr i (treeFieldLocs fields words children)
        (treeFieldTypes fields tys) := by
  induction fields generalizing tys words children i with
  | nil => rfl
  | cons bit rest ih =>
    cases bit <;> simp only [treeStoreFields, treeFieldLocs, treeFieldTypes, recordStoreCode, ih,
      List.headD_cons, List.tail_cons, slotIndex, toWordCode, List.append_assoc, List.cons_append,
      List.nil_append]

theorem treeLoadFields_eq (h ptr : Nat) (tys : List ValueType) (words children i : Nat)
    (fields : List Bool) :
    treeLoadFields h ptr tys words children i fields =
      recordLoadCode h ptr i (treeFieldLocs fields words children) (treeFieldTypes fields tys) := by
  induction fields generalizing tys words children i with
  | nil => rfl
  | cons bit rest ih =>
    cases bit <;> simp only [treeLoadFields, treeFieldLocs, treeFieldTypes, recordLoadCode, ih,
      List.headD_cons, List.tail_cons, slotIndex, ofWordCode, List.append_assoc, List.cons_append,
      List.nil_append]

end Verified
