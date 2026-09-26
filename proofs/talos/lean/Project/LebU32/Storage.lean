import Project.LebU32.Heap

namespace Project.LebU32.Spec
open Wasm Project.Common Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

structure RunningStorage (seed : Heap) (initial current : Store Unit) (count : Nat)
    (bytes : ByteArray) : Prop where
  heap : (runningHeap seed count).At current
  size : bytes.size = count
  values : PackedMemory.ByteArrayAt current.mem (bytePointer seed count).toNat bytes
  owner : 0 < count → (runningHeap seed count).OwnsPacked current (byteNode seed (count - 1)) bytes
  pages : current.mem.pages = initial.mem.pages
  cap : ∀ module_ index, current.memoryCap module_ index = initial.memoryCap module_ index
  low : ∀ address, address < seed.top.toNat → current.mem.bytes address = initial.mem.bytes address

structure PushedStorage (seed : Heap) (initial current : Store Unit) (count : Nat)
    (before : ByteArray) (value : UInt64) : Prop where
  heap : (finishedHeap seed (count + 1)).At current
  size : before.size = count
  output : (finishedHeap seed (count + 1)).OwnsPacked current (byteNode seed count) (before.push value.toUInt8)
  previous : 0 < count → (finishedHeap seed (count + 1)).OwnsPacked current (byteNode seed (count - 1)) before
  pages : current.mem.pages = initial.mem.pages
  cap : ∀ module_ index, current.memoryCap module_ index = initial.memoryCap module_ index
  low : ∀ address, address < seed.top.toNat → current.mem.bytes address = initial.mem.bytes address

theorem RunningStorage.initial (seed : Heap) (initial : Store Unit)
    (hHeap : seed.At initial) (hNodes : seed.nodes = []) :
    RunningStorage seed initial initial 0 ByteArray.empty := by
  refine ⟨?_, rfl, ?_, ?_, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · simpa only [runningHeap_zero seed hNodes] using hHeap
  · simp [PackedMemory.ByteArrayAt, bytePointer]
  · omega

theorem RunningStorage.protected {seed : Heap} {initial current : Store Unit} {count : Nat}
    {bytes : ByteArray} (h : RunningStorage seed initial current count bytes) :
    (runningHeap seed count).Protects (bytePointer seed count).toNat
      ((bytePointer seed count).toNat + bytes.size) := by
  by_cases hZero : count = 0
  · subst count
    refine ⟨by simp [bytePointer, h.size], ?_⟩
    simp [runningHeap]
  · simpa only [bytePointer, if_neg hZero] using (h.owner (by omega)).payload_protects

theorem RunningStorage.pushed {seed : Heap} {initial current final : Store Unit} {count : Nat}
    {bytes : ByteArray} (h : RunningStorage seed initial current count bytes) (value : UInt64)
    (hCount : count ≤ 4) (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPush : (runningHeap seed count).PackedOutput current final (PackedPush.need bytes) (bytes.push value.toUInt8))
    (hPages : final.mem.pages = ((runningHeap seed count).allocatePackedStore current (PackedPush.need bytes)).mem.pages) :
    PushedStorage seed initial final count bytes value := by
  have hNeed := byte_push_need bytes (by rw [h.size]; omega)
  rw [hNeed] at hPush hPages
  have hAllocate := running_allocate_heap seed count hCount
  have hNode := running_allocate_node seed count hCount
  have hFrame := hPush.frame
  refine ⟨?_, h.size, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hAllocate] using hPush.heapAt
  · simpa only [hAllocate, hNode] using hPush.owned
  · intro hPositive
    simpa only [hAllocate] using hFrame.ownsPacked hPush.heapAt (h.owner hPositive)
  · apply Nat.le_antisymm
    · rw [hPages]
      change (PackedAllocation.allocated current (runningHeap seed count).top 8 (runningHeap seed count).nodes).mem.pages ≤ initial.mem.pages
      rw [PackedAllocation.pages_eq]
      apply allocated_pages_bound current _ _ _ initial.mem.pages h.pages.le
      intro hNone
      have hBound := running_bump_bound seed count hFit hNone
      exact hBound.trans hMemory
    · rw [← h.pages]
      exact hFrame.pages
  · intro module_ index
    exact (hPush.memoryCap module_ index).trans (h.cap module_ index)
  · intro address hAddress
    exact (hFrame.bytes 0 seed.top.toNat (running_protects_low seed count hFit)
      address (Nat.zero_le _) hAddress).trans (h.low address hAddress)

theorem PushedStorage.first {seed : Heap} {initial current : Store Unit}
    {bytes : ByteArray} {value : UInt64} (h : PushedStorage seed initial current 0 bytes value) :
    RunningStorage seed initial current 1 (bytes.push value.toUInt8) := by
  refine ⟨h.heap, by rw [ByteArray.size_push, h.size], ?_, fun _ => h.output, h.pages, h.cap, h.low⟩
  simpa only [bytePointer, show ¬1 = 0 by decide, ite_false, Nat.reduceSub] using h.output.buffer.values

theorem byteNode_previous_separate (seed : Heap) (count : Nat)
    (hCount : count ≤ 4) (hPositive : 0 < count)
    (hFit : seed.top.toNat + 112 < 4294967296) :
    regionsDisjoint (byteNode seed count).region (byteNode seed (count - 1)).region := by
  simp only [regionsDisjoint, FreeNode.region, byteNode_toNat seed _ hFit,
    show ∀ i, (byteNode seed i).capacity.toNat = 8 from fun _ => rfl]
  interval_cases count <;> omega

theorem PushedStorage.released {seed : Heap} {initial current : Store Unit} {count : Nat}
    {bytes : ByteArray} {value : UInt64} (h : PushedStorage seed initial current count bytes value)
    (hCount : count ≤ 4) (hPositive : 0 < count)
    (hFit : seed.top.toNat + 112 < 4294967296) :
    let heap := finishedHeap seed (count + 1)
    let previous := byteNode seed (count - 1)
    RunningStorage seed initial (heap.releaseStore current previous) (count + 1) (bytes.push value.toUInt8) := by
  have hOld := h.previous hPositive
  have hRoot32 : (byteNode seed (count - 1)).root.toNat ≤ 4294967296 := by
    have := hOld.buffer.addressBound
    omega
  have hOwned := h.output.released (byteNode seed (count - 1)) hOld.buffer.rootBound hRoot32
    (byteNode_previous_separate seed count hCount hPositive hFit)
  have hHeap := (finishedHeap seed (count + 1)).release_at current (byteNode seed (count - 1))
    h.heap hOld.buffer.rootBound hOld.buffer.addressBound hOld.buffer.memoryBound
    hOld.buffer.fresh.capacityWord hOld.below hOld.separated
  rw [running_release_heap seed count hCount hPositive] at hOwned hHeap
  refine ⟨hHeap, by rw [ByteArray.size_push, h.size], ?_, ?_, h.pages, h.cap, ?_⟩
  · simpa only [bytePointer, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel] using hOwned.buffer.values
  · intro _
    simpa only [Nat.add_sub_cancel] using hOwned
  · intro address hAddress
    apply (releasedStore_bytes current (byteNode seed (count - 1)).root _ _ _
      hOld.buffer.rootBound hRoot32 address ?_).trans (h.low address hAddress)
    rw [byteNode_toNat seed (count - 1) hFit]
    exact Or.inl (by omega)

#print axioms RunningStorage.pushed
#print axioms PushedStorage.released
end Project.LebU32.Spec
