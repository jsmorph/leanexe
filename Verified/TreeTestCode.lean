import Verified.TreeCopyState
import Verified.TreeSelect

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def treeCopyCondition (mask : UInt64) (i : Nat) (word : UInt64) : UInt32 :=
  (if ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 then 0 else 1) &&&
    (if word = 0 then 0 else 1)

def copyBranch : LeanExe.Pipeline.Slot → UInt32
  | .child (.record _) => 1
  | _ => 0

/-- The condition of the slot test: the slot is a child pointer, and the word is not null. -/
theorem treeCopyCondition_spec {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {parent : UInt64} {record : CopyRecord} (h : record.Holds shape heap store parent)
    (hBound : record.next < record.slots.length)
    (hNotArray : ∀ words, record.slots[record.next] ≠ .array words)
    (hNotBytes : ∀ data, record.slots[record.next] ≠ .bytes data) :
    treeCopyCondition (maskOf record.slots) record.next
      (store.mem.read64 (slotAddress record.source record.next)) =
      copyBranch record.slots[record.next] := by
  obtain ⟨r, hLength, -, -, hLayout, -⟩ := id h.layout
  have hBit : ((maskOf record.slots >>> (UInt64.ofNat record.next % 64)) &&& 1) =
      record.slots[record.next].bit :=
    maskOf_test _ (by rw [hLength]; exact shape.width_le r) _ hBound
  have hBorrow := SlotsBorrowed.get record.slots 0 h.borrowed.2 record.next hBound
  simp only [Nat.zero_add] at hBorrow
  cases hSlot : record.slots[record.next] with
  | word value => simp [treeCopyCondition, hBit, hSlot, Slot.bit, copyBranch]
  | child value =>
    rw [hSlot] at hBorrow
    cases value with
    | null =>
      have hZero : store.mem.read64 (slotAddress record.source record.next) = 0 := hBorrow.1
      simp [treeCopyCondition, hBit, hSlot, Slot.bit, copyBranch, hZero]
    | record children =>
      have hNonzero := hBorrow.1.1.nonzero
      simp [treeCopyCondition, hBit, hSlot, Slot.bit, copyBranch, hNonzero]
  | array words => exact absurd hSlot (hNotArray words)
  | bytes data => exact absurd hSlot (hNotBytes data)

def treeCopyArrayCondition (mask : UInt64) (i : Nat) : UInt32 :=
  if ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 then 0 else 1

def arrayBranch : LeanExe.Pipeline.Slot → UInt32
  | .array _ => 1
  | _ => 0

/-- The condition of the array test: the slot is an array slot. -/
theorem treeCopyArrayCondition_spec {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {parent : UInt64} {record : CopyRecord} (h : record.Holds shape heap store parent)
    (hBound : record.next < record.slots.length) :
    treeCopyArrayCondition (arrayMaskOf record.slots) record.next =
      arrayBranch record.slots[record.next] := by
  obtain ⟨r, hLength, -, -, -, -⟩ := id h.layout
  have hBit := arrayMaskOf_test _ (by rw [hLength]; exact shape.width_le r) _ hBound
  unfold treeCopyArrayCondition
  rw [hBit]
  cases record.slots[record.next] <;> simp [Slot.arrayBit, arrayBranch]

def treeCopyBufferCondition (mask : UInt64) (i : Nat) : UInt32 :=
  if ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 then 0 else 1

def bufferBranch : LeanExe.Pipeline.Slot → UInt32
  | .bytes _ => 1
  | _ => 0

/-- The condition of the buffer test: the slot holds a buffer's root. -/
theorem treeCopyBufferCondition_spec {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {parent : UInt64} {record : CopyRecord} (h : record.Holds shape heap store parent)
    (hBound : record.next < record.slots.length) :
    treeCopyBufferCondition (bufferMaskOf record.slots) record.next =
      bufferBranch record.slots[record.next] := by
  obtain ⟨r, hLength, -, -, -, -⟩ := id h.layout
  have hBit := bufferMaskOf_test _ (by rw [hLength]; exact shape.width_le r) _ hBound
  unfold treeCopyBufferCondition
  rw [hBit]
  cases record.slots[record.next] <;> simp [Slot.bufferBit, bufferBranch]

#print axioms treeCopyCondition_spec
#print axioms treeCopyArrayCondition_spec
#print axioms treeCopyBufferCondition_spec
end Verified
