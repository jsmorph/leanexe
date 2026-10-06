import LeanExe.ProofKit.FixedArrayAllocate

/-!
# Runtime functions

Every compiled module contains `alloc` and `release`.  An object is a payload
preceded by a 48-byte header: the magic number, the count, the payload capacity,
the kind, the element width, and the child mask.  Every live object has one owner,
so its count is 1.  Globals 0 to 3 hold the bump pointer `top`, the free-list head,
and the allocation and free counters.

`release` does not recurse.  The released object joins a pending list linked
through its count field.  A loop takes each pending object,
drops the references its masked slots hold, and then returns its block to the
free list, whose link overwrites the child mask.  The free list is in address
order: the block goes before the first free block above it and merges with the
free blocks on either side when they touch.  `alloc` takes the first block that
fits and, when at least 56 bytes would remain, only its upper part.
-/

namespace LeanExe.Runtime

open Wasm

def magic : UInt64 := 5501223100278326855

/-- Pushes the header word `back` bytes before the payload at local `ptr`. -/
def headerLoad (ptr : Nat) (back : UInt64) : Program :=
  [.localGet ptr, .constI64 back, .subI64, .wrapI64, .load64 0]

/-- Stores the value `value` pushes into the header word `back` bytes before the
payload at local `ptr`. -/
def headerStore (ptr : Nat) (back : UInt64) (value : Program) : Program :=
  [.localGet ptr, .constI64 back, .subI64, .wrapI64] ++ value ++ [.store64 0]

def incrementGlobal (index : Nat) : Program :=
  [.globalGet index, .constI64 1, .addI64, .globalSet index]

/-- Traps unless the object at local `ptr` carries the magic number. -/
def checkMagic (ptr : Nat) : Program :=
  headerLoad ptr 48 ++ [.constI64 magic, .neI64, .iff 0 0 [.unreachable] []]

/-- Drops the one reference to the object at local `ptr`, using local `count`.  It
traps on a missing magic number or a count other than 1, which a second release of
the object would read, and links the object onto the pending list in local
`pending` through its count field. -/
def dropReference (ptr count pending : Nat) : Program :=
  checkMagic ptr ++ headerLoad ptr 40 ++
  [.localSet count, .localGet count, .constI64 1, .neI64, .iff 0 0 [.unreachable] []] ++
  headerStore ptr 40 [.localGet pending] ++ [.localGet ptr, .localSet pending]

/-- Runs `body` with local `index` from 0 while it is below local `bound`. -/
def countedLoop (index bound : Nat) (body : Program) : Program :=
  [.constI64 0, .localSet index,
   .block 0 0 [.loop 0 0
     ([.localGet index, .localGet bound, .geUI64, .br_if 1] ++ body ++
       [.localGet index, .constI64 1, .addI64, .localSet index, .br 0])]]

/-- Drops the reference in the slot whose address `address` pushes, unless the
slot is null, when bit `bit` of local `mask` is set. -/
def dropMaskedSlot (mask bit child count pending : Nat) (address : Program) : Program :=
  [.localGet mask, .localGet bit, .shrUI64, .constI64 1, .andI64, .constI64 0, .neI64,
   .iff 0 0
     (address ++ [.wrapI64, .load64 0, .localSet child,
       .localGet child, .constI64 0, .neI64,
       .iff 0 0 (dropReference child count pending) []])
     []]

/-- Locals of `release`: the parameter `ptr`, then these. -/
def releaseCount : Nat := 1
def releasePending : Nat := 2
def releaseObject : Nat := 3
def releaseKind : Nat := 4
def releaseLength : Nat := 5
def releaseWidth : Nat := 6
def releaseMask : Nat := 7
def releaseElement : Nat := 8
def releaseSlot : Nat := 9
def releaseChild : Nat := 10
def releasePrevious : Nat := 11
def releaseCurrent : Nat := 12

/-- Drops the references held by the object at local `releaseObject`: nothing when
its child mask is zero, and otherwise the masked slots of a record (kind 1) or
the masked slots of every element of an array (kind 2). -/
def dropChildren : Program :=
  let q := releaseObject
  let drop (address : Program) :=
    dropMaskedSlot releaseMask releaseSlot releaseChild releaseCount releasePending address
  headerLoad q 8 ++ [.localSet releaseMask, .localGet releaseMask, .constI64 0, .neI64,
   .iff 0 0
     (headerLoad q 24 ++ [.localSet releaseKind] ++
      headerLoad q 16 ++ [.localSet releaseWidth] ++
      [.localGet releaseKind, .constI64 1, .eqI64,
       .iff 0 0
         (countedLoop releaseSlot releaseWidth
           (drop [.localGet q, .localGet releaseSlot, .constI64 8, .mulI64, .addI64]))
         [],
       .localGet releaseKind, .constI64 2, .eqI64,
       .iff 0 0
         ([.localGet q, .wrapI64, .load64 0, .localSet releaseLength] ++
           countedLoop releaseElement releaseLength
             (countedLoop releaseSlot releaseWidth
               (drop [.localGet q, .constI64 8, .addI64,
                 .localGet releaseElement, .localGet releaseWidth, .mulI64,
                 .localGet releaseSlot, .addI64, .constI64 8, .mulI64, .addI64])))
         []])
     []]

/-- Finds the place of the block at local `releaseObject` in the free list:
`releasePrevious` ends at the last block at or below it, or 0, and
`releaseCurrent` at the first block above it, or 0. -/
def findPlace : Program :=
  [.constI64 0, .localSet releasePrevious, .globalGet 1, .localSet releaseCurrent,
   .block 0 0 [.loop 0 0
     ([.localGet releaseCurrent, .constI64 0, .eqI64, .br_if 1,
       .localGet releaseObject, .localGet releaseCurrent, .ltUI64, .br_if 1,
       .localGet releaseCurrent, .localSet releasePrevious] ++
      headerLoad releaseCurrent 8 ++ [.localSet releaseCurrent, .br 0])]]

/-- Merges the block at local `ptr` with the free block at local `next` when that
block starts where it ends, and otherwise links it to `next`. -/
def joinProgram (ptr next : Nat) : Program :=
  [.localGet ptr] ++ headerLoad ptr 32 ++
  [.addI64, .constI64 48, .addI64, .localGet next, .eqI64,
   .iff 0 0
     (headerStore ptr 32
        (headerLoad ptr 32 ++ [.constI64 48, .addI64] ++ headerLoad next 32 ++ [.addI64]) ++
       headerStore ptr 8 (headerLoad next 8))
     (headerStore ptr 8 [.localGet next])]

/-- Returns the block of the object at local `releaseObject` to the free list. -/
def freeObject : Program :=
  incrementGlobal 3 ++ headerStore releaseObject 40 [.constI64 0] ++ findPlace ++
  joinProgram releaseObject releaseCurrent ++
  [.localGet releasePrevious, .constI64 0, .eqI64,
   .iff 0 0 [.localGet releaseObject, .globalSet 1] (joinProgram releasePrevious releaseObject)]

def releaseBody : Program :=
  [.localGet 0, .constI64 0, .eqI64, .iff 0 0 [.ret] [],
   .constI64 0, .localSet releasePending] ++
  dropReference 0 releaseCount releasePending ++
  [.block 0 0 [.loop 0 0
    ([.localGet releasePending, .constI64 0, .eqI64, .br_if 1,
      .localGet releasePending, .localSet releaseObject] ++
      headerLoad releaseObject 40 ++ [.localSet releasePending] ++
      dropChildren ++ freeObject ++ [.br 0])]]

def releaseFunction (typeIdx : Nat) : Wasm.Function :=
  { params := [.i64], locals := List.replicate 12 .i64, body := releaseBody, results := [],
    typeIdx := some typeIdx }

/-- `alloc bytes` returns a fresh object with count one whose payload holds at
least `bytes` bytes, rounded up to a multiple of 8 and at least 8.  The header
describes an array of one-word elements with no child pointers.  The allocation
itself is `FixedArrayAllocate.program`, which reuses the first free block that
fits and otherwise bumps `top`, growing memory as needed, and counts the
allocation. -/
def allocBody : Program :=
  [.localGet 0, .constI64 7, .addI64, .constI64 8, .divUI64, .constI64 8, .mulI64,
   .localSet 1, .localGet 1, .constI64 8, .ltUI64, .iff 0 0 [.constI64 8, .localSet 1] []] ++
  LeanExe.ProofKit.FixedArrayAllocate.program 1 1 ++ [.localGet 6]

def allocFunction (typeIdx : Nat) : Wasm.Function :=
  { params := [.i64], locals := List.replicate 6 .i64, body := allocBody, results := [.i64],
    typeIdx := some typeIdx }

end LeanExe.Runtime
