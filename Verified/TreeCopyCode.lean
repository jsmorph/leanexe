import Verified.Tree
import Verified.ArrayCopyCode
import LeanExe.Runtime.Defs

namespace Verified

open Wasm LeanExe.Runtime

def treeCopyScratch : Nat := 6

def treeSlotAddress (ptr index : Nat) : Program :=
  [.localGet ptr, .localGet index, .constI64 8, .mulI64, .addI64, .wrapI64]

/-- Code that pushes the word paired with the tag that `tag` pushes: tests of the tag against each
pair's first word in order, the last pair untested. -/
def selectChain (tag : Program) : List (UInt64 × UInt64) → Program
  | [] => [.constI64 0]
  | [(_, v)] => [.constI64 v]
  | (i, v) :: p :: rest =>
    tag ++ [.constI64 i, .eqI64, .iff 0 1 [.constI64 v] (selectChain tag (p :: rest)) [] [.i64]]

/-- Code that pushes `value r` for the record constructor `r` whose tag `tag` pushes.  For an
untagged shape it is the word of the single record constructor, and `tag` does not run. -/
def TreeShape.selectCode (shape : TreeShape) (tag : Program)
    (value : Fin shape.records → UInt64) : Program :=
  selectChain tag (shape.tagPairs value)

/-- The tag of the record at local `ptr`: its slot 0. -/
def treeTagCode (ptr : Nat) : Program := [.localGet ptr, .wrapI64, .load64 0]

/-- The allocation of a record of `width` slots into local `dst`. -/
def recordAllocate (width dst : Nat) : Program :=
  [.constI64 (8 * UInt64.ofNat width), .call 0, .localSet dst]

def treeCopyAllocate (shape : TreeShape) (src dst : Nat) : Program :=
  shape.selectCode (treeTagCode src) (fun r => 8 * UInt64.ofNat (shape.width r)) ++
    [.call 0, .localSet dst]

/-- Starts the copy of a record into the block at local `dst`.  For a tagged shape the width,
selected by the tag of the source record at local `src`, goes into the width word.  The parent
link, the source pointer, and the next slot index then go into the header. -/
def treeCopyBegin (shape : TreeShape) (src dst : Nat) (input parent : Program) : Program :=
  (if shape.tagged then
    headerStore dst 16 (shape.selectCode (treeTagCode src) fun r => UInt64.ofNat (shape.width r))
  else []) ++
    headerStore dst 40 parent ++ headerStore dst 24 input ++ headerStore dst 8 [.constI64 0]

def treeCopyAdvance (ptr index : Nat) : Program :=
  headerStore ptr 8 [.localGet index, .constI64 1, .addI64]

def treeCopyRead (base : Nat) : Program :=
  headerLoad (base + 1) 24 ++ [.localSet (base + 3)] ++
    treeSlotAddress (base + 3) (base + 2) ++ [.load64 0, .localSet (base + 4)]

def treeCopyTest (shape : TreeShape) (base : Nat) : Program :=
  shape.selectCode (treeTagCode (base + 3)) shape.mask ++
    [.localGet (base + 2), .shrUI64, .constI64 1, .andI64, .eqzI64,
      .eqz, .localGet (base + 4), .eqzI64, .eqz, .and]

/-- The test of whether the slot whose index local `base + 2` holds is an array slot of the record
whose source local `base + 3` holds. -/
def treeCopyArrayTest (shape : TreeShape) (base : Nat) : Program :=
  shape.selectCode (treeTagCode (base + 3)) shape.arrayMask ++
    [.localGet (base + 2), .shrUI64, .constI64 1, .andI64, .eqzI64, .eqz]

/-- The copy of an array slot.  The array whose address local `base + 4` holds goes to a new
block, with locals `base + 2` to `base + 5` as scratch.  The new address goes to local `base + 4`,
the slot index goes back to local `base + 2` from the header, and the address goes into the slot
as a word does. -/
def treeCopyArray (base : Nat) : Program :=
  [.localGet (base + 4), .localSet (base + 2)] ++ copyArrayCode (base + 2) (base + 3) ++
    [.localSet (base + 4)] ++ headerLoad (base + 1) 8 ++ [.localSet (base + 2)] ++
    treeSlotAddress (base + 1) (base + 2) ++ [.localGet (base + 4), .store64 0] ++
    treeCopyAdvance (base + 1) (base + 2)

/-- One step of the copy loop: the copy of the slot of the record being copied that local
`base + 2` indexes.  For a shape with array fields, an array slot goes to `treeCopyArray` first,
and the code for a shape without them has no array test. -/
def treeCopySlot (shape : TreeShape) (base : Nat) : Program :=
  let current := base + 1
  let index := base + 2
  let value := base + 4
  let fresh := base + 5
  let copyWord :=
    treeSlotAddress current index ++ [.localGet value, .store64 0] ++ treeCopyAdvance current index
  let descend := treeCopyAllocate shape value fresh ++
    treeCopyBegin shape value fresh [.localGet value] [.localGet current] ++
    [.localGet fresh, .localSet current]
  let other := treeCopyTest shape base ++ [.iff 0 0 descend copyWord]
  treeCopyRead base ++
    if shape.hasArrays then treeCopyArrayTest shape base ++ [.iff 0 0 (treeCopyArray base) other]
    else other

/-- Restores the header of the copied record at local `ptr`, whose slot 0 holds its tag when the
shape is tagged: count 1, kind 1, and the width and mask of its record constructor. -/
def restoreRecordCode (shape : TreeShape) (ptr : Nat) : Program :=
  headerStore ptr 40 [.constI64 1] ++ headerStore ptr 24 [.constI64 1] ++
    headerStore ptr 16 (shape.selectCode (treeTagCode ptr) fun r => UInt64.ofNat (shape.width r)) ++
    headerStore ptr 8 (shape.selectCode (treeTagCode ptr) shape.mask)

def treeCopyFinish (shape : TreeShape) (base : Nat) : Program :=
  let current := base + 1
  let index := base + 2
  let fresh := base + 5
  headerLoad current 40 ++ [.localSet fresh] ++
    restoreRecordCode shape current ++
    [.localGet fresh, .eqzI64, .br_if 2] ++
    headerLoad fresh 8 ++ [.localSet index] ++ treeSlotAddress fresh index ++
    [.localGet current, .store64 0] ++ treeCopyAdvance fresh index ++
    [.localGet fresh, .localSet current]

/-- The width of the record being copied: a constant for an untagged shape, and otherwise the
width word that `treeCopyBegin` stored. -/
def treeCopyWidth (shape : TreeShape) (base : Nat) : Program :=
  if shape.tagged then headerLoad (base + 1) 16
  else shape.selectCode [] fun r => UInt64.ofNat (shape.width r)

def treeCopyBody (shape : TreeShape) (base : Nat) : Program :=
  headerLoad (base + 1) 8 ++
    [.localSet (base + 2), .localGet (base + 2)] ++ treeCopyWidth shape base ++
      [.ltUI64, .iff 0 0 (treeCopySlot shape base) (treeCopyFinish shape base), .br 0]

def treeCopyCode (shape : TreeShape) (src base : Nat) : Program :=
  let result := base
  let current := base + 1
  [.localGet src, .eqzI64, .iff 0 1 [.constI64 0]
    (treeCopyAllocate shape src result ++
      treeCopyBegin shape src result [.localGet src] [.constI64 0] ++
      [.localGet result, .localSet current,
       .block 0 0 [.loop 0 0 (treeCopyBody shape base)],
       .localGet result]) [] [.i64]]

end Verified
