import Verified.Tree
import LeanExe.Runtime.Defs

namespace Verified

open Wasm LeanExe.Runtime

def treeCopyScratch : Nat := 6

def treeSlotAddress (ptr index : Nat) : Program :=
  [.localGet ptr, .localGet index, .constI64 8, .mulI64, .addI64, .wrapI64]

def treeCopyAllocate (shape : TreeShape) (dst : Nat) : Program :=
  [.constI64 (8 * UInt64.ofNat shape.fields.length), .call 0, .localSet dst]

def treeCopyBegin (dst : Nat) (input parent : Program) : Program :=
  headerStore dst 40 parent ++ headerStore dst 24 input ++ headerStore dst 8 [.constI64 0]

def treeCopyAdvance (ptr index : Nat) : Program :=
  headerStore ptr 8 [.localGet index, .constI64 1, .addI64]

def treeCopyRead (base : Nat) : Program :=
  headerLoad (base + 1) 24 ++ [.localSet (base + 3)] ++
    treeSlotAddress (base + 3) (base + 2) ++ [.load64 0, .localSet (base + 4)]

def treeCopyTest (shape : TreeShape) (base : Nat) : Program :=
  [.constI64 shape.mask, .localGet (base + 2), .shrUI64, .constI64 1, .andI64, .eqzI64,
    .eqz, .localGet (base + 4), .eqzI64, .eqz, .and]

def treeCopySlot (shape : TreeShape) (base : Nat) : Program :=
  let current := base + 1
  let index := base + 2
  let value := base + 4
  let fresh := base + 5
  let copyWord :=
    treeSlotAddress current index ++ [.localGet value, .store64 0] ++ treeCopyAdvance current index
  let descend := treeCopyAllocate shape fresh ++
    treeCopyBegin fresh [.localGet value] [.localGet current] ++
    [.localGet fresh, .localSet current]
  treeCopyRead base ++ treeCopyTest shape base ++ [.iff 0 0 descend copyWord]

def restoreRecordCode (shape : TreeShape) (ptr : Nat) : Program :=
  headerStore ptr 40 [.constI64 1] ++ headerStore ptr 24 [.constI64 1] ++
    headerStore ptr 16 [.constI64 (UInt64.ofNat shape.fields.length)] ++
    headerStore ptr 8 [.constI64 shape.mask]

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

def treeCopyBody (shape : TreeShape) (base : Nat) : Program :=
  headerLoad (base + 1) 8 ++
    [.localSet (base + 2), .localGet (base + 2), .constI64 (UInt64.ofNat shape.fields.length),
      .ltUI64, .iff 0 0 (treeCopySlot shape base) (treeCopyFinish shape base), .br 0]

def treeCopyCode (shape : TreeShape) (src base : Nat) : Program :=
  let result := base
  let current := base + 1
  [.localGet src, .eqzI64, .iff 0 1 [.constI64 0]
    (treeCopyAllocate shape result ++ treeCopyBegin result [.localGet src] [.constI64 0] ++
      [.localGet result, .localSet current,
       .block 0 0 [.loop 0 0 (treeCopyBody shape base)],
       .localGet result]) [] [.i64]]

end Verified
