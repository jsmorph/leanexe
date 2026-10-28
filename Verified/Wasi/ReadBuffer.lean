import Verified.Wasi.ReadFrame
import LeanExe.Wasi.Semantics

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem read_payload_region {heap : Heap} {store : Store Unit} {root : UInt64}
    {previous : LeanExe.Bytes} {capacity : Nat}
    (h : Heap.Buffer heap store root previous)
    (hCapacity : capacity ≤ capacityAt store root) : heap.Region (root.toNat, capacity) := by
  refine ⟨by have := h.object.below; omega, ?_⟩
  intro node hNode
  have hApart := h.object.separate node hNode
  have hBase := h.object.base
  simp only [regionsDisjoint] at hApart ⊢
  omega

theorem read_capacity {before after : Store World} {heap : Heap} {root : UInt64}
    {capacity : Nat} {previous : LeanExe.Bytes}
    (h : Heap.Buffer heap (PureTransport.erase before) root previous)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity)]) :
    capacityAt (PureTransport.erase after) root = capacityAt (PureTransport.erase before) root := by
  unfold capacityAt
  apply congrArg UInt64.toNat
  apply Memory.read64_congr
  intro index hi
  have hBase := h.object.base
  have hAddress := h.object.address
  rw [headerAddress_toNat (by change 32 ≤ root.toNat; omega) (by omega)]
  simp only [UInt64.reduceToNat]
  apply hFrame.bytes
  intro region hRegion
  rcases List.mem_cons.mp hRegion with rfl | hRegion
  · dsimp only [InRange, ABI.scratch]
    omega
  · obtain rfl := List.mem_singleton.mp hRegion
    dsimp only [InRange]
    omega

theorem read_empty_at {before after : Store World} {heap : Heap} {root : UInt64}
    {capacity : Nat} {previous : LeanExe.Bytes}
    (h : Heap.Buffer heap (PureTransport.erase before) root previous)
    (hHeap : heap.At (PureTransport.erase before))
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity)]) :
    Bytes.At after.mem root LeanExe.Bytes.empty := by
  have hAddress := h.object.address
  have hBelow := h.object.below
  have hTop := hHeap.top
  refine ⟨?_, ?_, ?_⟩
  · change root.toNat + 0 ≤ 4294967296
    omega
  · change root.toNat + 0 ≤ after.mem.pages * 65536
    rw [hFrame.pages]
    change root.toNat ≤ (PureTransport.erase before).mem.pages * 65536
    omega
  · intro index hi
    change index < 0 at hi
    omega

theorem read_buffer {World : Type} {host : Host World} {before after : Store World}
    {heap : Heap} {root capacity errno : UInt64} {previous committed : LeanExe.Bytes}
    (h : Heap.Buffer heap (PureTransport.erase before) root previous)
    (hHeap : heap.At (PureTransport.erase before))
    (hCapacity : capacity.toNat ≤ capacityAt (PureTransport.erase before) root)
    (hRead : host.read before.host capacity (.returned errno committed) after.host)
    (hFrame : GuestFrame before after [ABI.scratch, (root.toNat, capacity.toNat)])
    (hData : errno = 0 → Bytes.At after.mem root committed) :
    heap.At (PureTransport.erase after) ∧
      Heap.Buffer heap (PureTransport.erase after) root (readResult errno committed).bytes ∧
      capacityAt (PureTransport.erase after) root =
        capacityAt (PureTransport.erase before) root := by
  have hStep := hFrame.readStep hHeap (read_payload_region h hCapacity)
  refine ⟨hStep.at_, ?_, read_capacity h hFrame⟩
  by_cases hZero : errno = 0
  · simp only [readResult, hZero, ite_true]
    exact allocated_afterRead h hFrame ((host.read_bound hRead).1.trans hCapacity) (hData hZero)
  · simp only [readResult, ite_eq_right hZero]
    exact allocated_afterRead h hFrame (by change 0 ≤ _; omega) (read_empty_at h hHeap hFrame)

end Verified.Wasi
