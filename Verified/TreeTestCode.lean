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

/-- The mask code of the slot test pushes the mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.maskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.mask) store s
      (maskOf record.slots) := by
  obtain ⟨r, -, hMask, hPrefix, -⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hMask]
  exact PushesWord.selectCode r shape.mask (PushesWord.tag hSrc hRoom)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

/-- The mask code of the array test pushes the array mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.arrayMaskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.arrayMask) store s
      (arrayMaskOf record.slots) := by
  obtain ⟨r, -, -, hPrefix, -, hArrays, -⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hArrays]
  exact PushesWord.selectCode r shape.arrayMask (PushesWord.tag hSrc hRoom)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

theorem wp_treeCopyArrayTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.arrayMask) store
      s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyArrayCondition mask i) :: s.values } host) :
    wp m (treeCopyArrayTest shape base ++ rest) Q store s host := by
  rw [treeCopyArrayTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    simpa [wp_simp, hIndex, treeCopyArrayCondition, hBit] using hNext

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

/-- The mask code of the buffer test pushes the buffer mask of the record whose source is at local
`src`. -/
theorem CopyRecord.Holds.bufferMaskPushes {m : Module} {host : HostEnv Unit} {shape : TreeShape}
    {heap : Heap} {store : Store Unit} {parent : UInt64} {record : CopyRecord} {s : Locals}
    {src : Nat} (h : record.Holds shape heap store parent) (hHeap : heap.At store)
    (hSrc : s.get src = some (.i64 record.source)) :
    PushesWord m host (shape.selectCode (treeTagCode src) shape.bufferMask) store s
      (bufferMaskOf record.slots) := by
  obtain ⟨r, -, -, hPrefix, -, -, hBuffers⟩ := id h.layout
  have hSlotted : record.slots ≠ [] := (NodeLayout.slotted h.layout).1
  obtain ⟨-, hRoom⟩ := NodeBorrowed.tagRoom h.borrowed hHeap hSlotted
  rw [hBuffers]
  exact PushesWord.selectCode r shape.bufferMask (PushesWord.tag hSrc hRoom)
    (fun ht => NodeBorrowed.tag h.borrowed hPrefix ht)

theorem wp_treeCopyBufferTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.bufferMask) store
      s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyBufferCondition mask i) :: s.values } host) :
    wp m (treeCopyBufferTest shape base ++ rest) Q store s host := by
  rw [treeCopyBufferTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    simpa [wp_simp, hIndex, treeCopyBufferCondition, hBit] using hNext

theorem wp_treeCopyTest {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {base i : Nat} {word mask : UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hMask : PushesWord m host (shape.selectCode (treeTagCode (base + 3)) shape.mask) store s mask)
    (hIndex : s.get (base + 2) = some (.i64 (UInt64.ofNat i)))
    (hWord : s.get (base + 4) = some (.i64 word))
    (hNext : wp m rest Q store
      { s with values := .i32 (treeCopyCondition mask i word) :: s.values } host) :
    wp m (treeCopyTest shape base ++ rest) Q store s host := by
  rw [treeCopyTest, List.append_assoc]
  apply hMask s.values
  simp only [Locals.get] at hIndex hWord
  by_cases hBit : ((mask >>> (UInt64.ofNat i % 64)) &&& 1) = 0 <;>
    by_cases hZero : word = 0 <;>
    simpa [wp_simp, hIndex, hWord, treeCopyCondition, hBit, hZero] using hNext

#print axioms treeCopyCondition_spec
#print axioms CopyRecord.Holds.maskPushes
#print axioms wp_treeCopyTest
#print axioms treeCopyArrayCondition_spec
#print axioms CopyRecord.Holds.arrayMaskPushes
#print axioms wp_treeCopyArrayTest
#print axioms treeCopyBufferCondition_spec
#print axioms CopyRecord.Holds.bufferMaskPushes
#print axioms wp_treeCopyBufferTest

end Verified
