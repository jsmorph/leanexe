import Verified.TreeSlotCode
import Verified.Bytes.Copy

/-! The copy loop's step for a buffer's root slot: a copy of the buffer into a new object, or
root 0 for an empty buffer, whose root goes into the slot.  The next step copies the buffer's
length, in the following slot, as a word. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyProgress.trapCost {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord} {m : Module}
    {Q : Assertion Unit}
    (h : CopyProgress shape heap0 initial root result limit heap store current parents)
    {cost : Nat} (hCharge : cost ≤ (current.work parents).cost)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q) :
    TrapOK (!decide (heap.Within store m cost)) Q := by
  by_cases hTotal : limit ≤ 65536 * initial.memoryCap m 0
  · have hWithin : heap.Within store m cost := by
      rw [Heap.Within, h.step.cap m]
      have := h.budget
      omega
    simp only [hWithin, decide_true, Bool.not_true, TrapOK]
  · by_cases hWithin : heap.Within store m cost
    · simp only [hWithin, decide_true, Bool.not_true, TrapOK]
    · simpa only [hTotal, hWithin, decide_false, Bool.not_false, TrapOK] using hTrap

theorem CopyRecord.work_bytes {current : CopyRecord} {parents : List CopyRecord}
    {data : LeanExe.Bytes} (h : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .bytes data) :
    CopyWork.Step (current.work parents) ({ current with next := current.next + 1 }.work parents) := by
  unfold CopyRecord.work
  rw [List.drop_eq_getElem_cons h, hSlot]
  exact .bytes

/-- The value of a buffer slot that the copy writes: the root of a copy of the buffer, which is 0
for an empty buffer. -/
theorem _root_.LeanExe.Pipeline.Bytes.Rep.slotOwned
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {data : LeanExe.Bytes} (h : Bytes.Rep heap store root length data)
    (hZero : length = 0 → root = 0) :
    (Slot.bytes data).ValueOwned heap store root := by
  rcases h.buffer with hEmpty | hBuffer
  · exact Or.inl hEmpty
  · by_cases hSize : data.data.size = 0
    · have hLength : length = 0 := by
        apply UInt64.toNat_inj.mp
        rw [h.length_eq, hSize]
        rfl
      exact Or.inl ⟨hZero hLength, hSize⟩
    · exact Or.inr ⟨hSize, hBuffer⟩

theorem _root_.LeanExe.Pipeline.Bytes.Rep.slotBlocks
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {data : LeanExe.Bytes} (h : Bytes.Rep heap store root length data)
    (hZero : length = 0 → root = 0) :
    (Slot.bytes data).valueBlocks store root = Bytes.regions store root := by
  rcases h.slotOwned hZero with ⟨rfl, hEmpty⟩ | ⟨hSize, hBuffer⟩
  · simp [Slot.valueBlocks, bufferRoots, hEmpty, Bytes.regions]
  · simp [Slot.valueBlocks, bufferRoots, hSize, Bytes.regions, hBuffer.nonzero]

end Verified
