import Verified.TreeMemory
import Verified.TreeNodeLayout
import LeanExe.Pipeline.RecordSlots

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

structure CopyRecord where
  source : UInt64
  pointer : UInt64
  slots : List LeanExe.Pipeline.Slot
  next : Nat

def CopyRecord.blocks (record : CopyRecord) (store : Store Unit) : List (Nat × Nat) :=
  block store record.pointer :: slotsBlocks store record.pointer 0 (record.slots.take record.next)

structure CopyRecord.Holds (shape : TreeShape) (heap : Heap) (store : Store Unit)
    (parent : UInt64) (record : CopyRecord) : Prop where
  layout : NodeLayout shape (.record record.slots)
  bound : record.next ≤ record.slots.length
  storage : RecordStorage record.slots.length heap store record.pointer
  borrowed : NodeBorrowed heap store record.source (.record record.slots)
  parent : store.mem.read64 (record.pointer - 40).toUInt32 = parent
  source : store.mem.read64 (record.pointer - 24).toUInt32 = record.source
  width : shape.tagged = true →
    store.mem.read64 (record.pointer - 16).toUInt32 = UInt64.ofNat record.slots.length
  index : store.mem.read64 (record.pointer - 8).toUInt32 = UInt64.ofNat record.next
  filled : SlotsOwned heap store record.pointer 0 (record.slots.take record.next)

theorem CopyRecord.Holds.frame {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {parent : UInt64} {record : CopyRecord}
    (h : record.Holds shape heap store parent)
    (hBytes : ∀ a, record.pointer.toNat - 48 ≤ a →
      a < record.pointer.toNat + capacityAt store record.pointer →
        store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store record.pointer))
    (hSource : ∀ r ∈ (Node.record record.slots).slotRegions store record.source,
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → store'.mem.bytes a = store.mem.bytes a) ∧ heap'.Region r)
    (hChildren : ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next),
      (∀ a, b.1 ≤ a → a < b.1 + b.2 → store'.mem.bytes a = store.mem.bytes a) ∧ heap'.Region b) :
    record.Holds shape heap' store' parent ∧ record.blocks store' = record.blocks store := by
  obtain ⟨hStorage, hCapacity⟩ := h.storage.frame hBytes hRegion
  obtain ⟨hBorrowed, _⟩ := NodeBorrowed.frame record.source (.record record.slots) h.borrowed hSource
  have hBase := h.storage.base
  have hRoom := h.storage.capacity
  have hAddress := h.storage.address
  have hBound := h.bound
  have hTaken : (record.slots.take record.next).length = record.next :=
    List.length_take_of_le h.bound
  obtain ⟨hPrefix, hBlocks⟩ := SlotsOwned.frame record.pointer 0
    (record.slots.take record.next) h.filled (by rw [hTaken]; omega)
    (fun a hLow hHigh => hBytes a (by omega) (by rw [hTaken] at hHigh; omega)) hChildren
  have hRead (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      store'.mem.read64 (record.pointer - back).toUInt32 =
        store.mem.read64 (record.pointer - back).toUInt32 := by
    apply Memory.read64_congr
    intro i hi
    rw [headerAddress_toNat (by omega) (by omega)]
    exact hBytes _ (by omega) (by omega)
  refine ⟨⟨h.layout, h.bound, hStorage, hBorrowed,
    (hRead 40 (by decide) (by decide)).trans h.parent,
    (hRead 24 (by decide) (by decide)).trans h.source,
    fun ht => (hRead 16 (by decide) (by decide)).trans (h.width ht),
    (hRead 8 (by decide) (by decide)).trans h.index, hPrefix⟩, ?_⟩
  simp only [CopyRecord.blocks, block_eq hCapacity, hBlocks]

def CopyRecord.work (current : CopyRecord) (parents : List CopyRecord) : CopyWork :=
  .current (current.slots.drop current.next)
    (parents.map fun record => record.slots.drop (record.next + 1))

#print axioms CopyRecord.Holds.frame

end Verified
