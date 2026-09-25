import Project.ProofKit.OwnedPacked

namespace Project.ProofKit
open Project.Runtime

def statusRoot (status : UInt64) (node : FreeNode) : UInt64 :=
  if status = 0 then node.root else 0

end Project.ProofKit

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit PackedMemory

structure Heap.StatusPacked (heap : Heap) (store : Store Unit) (status : UInt64)
    (node : FreeNode) (bytes : ByteArray) : Prop where
  owned : status = 0 → heap.OwnsPacked store node bytes
  empty : status ≠ 0 → bytes = .empty

theorem Heap.StatusPacked.values {heap : Heap} {store : Store Unit} {status : UInt64}
    {node : FreeNode} {bytes : ByteArray} (h : heap.StatusPacked store status node bytes) :
    ByteArrayAt store.mem (statusRoot status node).toNat bytes := by
  by_cases hZero : status = 0
  · simpa only [statusRoot, hZero, ite_true] using (h.owned hZero).buffer.values
  · simp [statusRoot, hZero, h.empty hZero, ByteArrayAt]

theorem Heap.StatusPacked.protects {heap : Heap} {store : Store Unit} {status : UInt64}
    {node : FreeNode} {bytes : ByteArray} (h : heap.StatusPacked store status node bytes) :
    heap.Protects (statusRoot status node).toNat ((statusRoot status node).toNat + bytes.size) := by
  by_cases hZero : status = 0
  · simpa only [statusRoot, hZero, ite_true] using (h.owned hZero).payload_protects
  · simp only [statusRoot, hZero, ite_false, h.empty hZero, ByteArray.size_empty,
      UInt64.toNat_zero, Nat.zero_add]
    exact ⟨Nat.zero_le _, fun _ _ => Or.inl (Nat.zero_le _)⟩

theorem Heap.Frame.statusPacked {before after : Heap} {initial final : Store Unit}
    (hFrame : before.Frame initial after final) (hHeap : after.At final)
    {status : UInt64} {node : FreeNode} {bytes : ByteArray}
    (h : before.StatusPacked initial status node bytes) : after.StatusPacked final status node bytes :=
  ⟨fun hZero => hFrame.ownsPacked hHeap (h.owned hZero), h.empty⟩

theorem Heap.StatusPacked.released {heap : Heap} {store : Store Unit} {status : UInt64}
    {source : FreeNode} {bytes : ByteArray} (h : heap.StatusPacked store status source bytes)
    (node : FreeNode) (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : status = 0 → regionsDisjoint source.region node.region) :
    (heap.release node).StatusPacked (heap.releaseStore store node) status source bytes :=
  ⟨fun hZero => (h.owned hZero).released node hRoot hRoot32 (hSep hZero), h.empty⟩

theorem Heap.OwnsPacked.root_ne_status {heap : Heap} {store : Store Unit}
    {node : FreeNode} {bytes : ByteArray} (h : heap.OwnsPacked store node bytes)
    (status : UInt64) (other : FreeNode)
    (hSep : status = 0 → regionsDisjoint node.region other.region) :
    node.root ≠ statusRoot status other := by
  by_cases hZero : status = 0
  · simpa only [statusRoot, hZero, ite_true] using h.root_ne (hSep hZero)
  · simp only [statusRoot, hZero, ite_false]
    intro hRoot
    have hBound := h.buffer.rootBound
    rw [hRoot] at hBound
    contradiction

#print axioms Heap.StatusPacked.values
#print axioms Heap.StatusPacked.protects
#print axioms Heap.Frame.statusPacked
#print axioms Heap.StatusPacked.released
#print axioms Heap.OwnsPacked.root_ne_status
end Project.EulerRiemann.Execution
