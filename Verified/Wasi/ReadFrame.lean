import Verified.Wasi.GuestFrame
import Verified.Bytes.Basic

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem GuestFrame.readStep {before after : Store World} {heap : Heap}
    {root : UInt64} {capacity : Nat}
    (h : GuestFrame before after [ABI.scratch, (root.toNat, capacity)])
    (hHeap : heap.At (PureTransport.erase before))
    (hPayload : heap.Region (root.toNat, capacity)) :
    Step heap (PureTransport.erase before)
      (fun kept => regionsDisjoint kept ABI.scratch ∧
        regionsDisjoint kept (root.toNat, capacity))
      heap (PureTransport.erase after) [] := by
  apply (h.step hHeap ?_).mono (by simp) (by simp)
  intro node hNode region hRegion
  rcases List.mem_cons.mp hRegion with rfl | hRegion
  · have hBase := hHeap.above node hNode
    right
    dsimp only [FreeNode.region, ABI.scratch]
    omega
  · obtain rfl := List.mem_singleton.mp hRegion
    exact hPayload.separate node hNode

theorem allocated_afterRead {before after : Store World} {heap : Heap}
    {root : UInt64} {capacity : Nat} {previous bytes : LeanExe.Bytes}
    (h : Bytes.Allocated heap (PureTransport.erase before) root previous)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity)])
    (hSize : bytes.data.size ≤ capacityAt (PureTransport.erase before) root)
    (hData : Bytes.At after.mem root bytes) :
    Bytes.Allocated heap (PureTransport.erase after) root bytes := by
  have hBase := h.object.base
  have hFit := h.object.address
  have hRead (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      after.mem.read64 (root - offset).toUInt32 =
        before.mem.read64 (root - offset).toUInt32 := by
    apply Memory.read64_congr
    intro index hi
    rw [headerAddress_toNat (by omega) (by omega)]
    apply hFrame.bytes
    intro region hRegion
    rcases List.mem_cons.mp hRegion with rfl | hRegion
    · dsimp only [InRange, ABI.scratch]
      omega
    · obtain rfl := List.mem_singleton.mp hRegion
      dsimp only [InRange]
      omega
  have hCapacity : capacityAt (PureTransport.erase after) root =
      capacityAt (PureTransport.erase before) root := by
    unfold capacityAt
    exact congrArg UInt64.toNat (hRead 32 (by decide) (by decide))
  refine ⟨⟨hBase, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hData.contents⟩
  · rw [hCapacity]; exact h.object.address
  · rw [hCapacity]; exact h.object.below
  · rw [hCapacity]; exact h.object.separate
  · exact (hRead 48 (by decide) (by decide)).trans h.magic
  · exact (hRead 40 (by decide) (by decide)).trans h.count
  · rw [hCapacity]; exact h.minimum
  · rw [hCapacity]; exact hSize
  · exact (hRead 24 (by decide) (by decide)).trans h.kind
  · exact (hRead 16 (by decide) (by decide)).trans h.width
  · exact (hRead 8 (by decide) (by decide)).trans h.childMask

end Verified.Wasi
