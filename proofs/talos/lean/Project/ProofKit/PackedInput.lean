import Project.ProofKit.OwnedPacked

namespace Project.ProofKit.PackedInput
open Wasm PackedMemory Project.EulerRiemann.Execution

def write (store : Store Unit) (base : Nat) (bytes : ByteArray) : Store Unit :=
  { store with mem := { store.mem with
      bytes := fun address =>
        if base ≤ address ∧ address < base + bytes.size then bytes[address - base]!
        else store.mem.bytes address } }

theorem writesRange (store : Store Unit) (base : Nat) (bytes : ByteArray) :
    Memory.WritesRange store (write store base bytes) base (base + bytes.size) := by
  refine ⟨rfl, rfl, ?_⟩
  intro address h
  simp [write, show ¬(base ≤ address ∧ address < base + bytes.size) by omega]

theorem represented (store : Store Unit) (base : Nat) (bytes : ByteArray)
    (hAddress : base + bytes.size ≤ 2^32)
    (hMemory : base + bytes.size ≤ store.mem.pages * 65536) :
    ByteArrayAt (write store base bytes).mem base bytes := by
  refine ⟨hAddress, hMemory, ?_⟩
  intro index hIndex
  simp [write, hIndex]

theorem allocated (heap : Project.EulerRiemann.Execution.Heap) (store : Store Unit)
    (need : UInt64) (bytes : ByteArray) (hHeap : heap.At store) (hNeed : bytes.size ≤ need.toNat)
    (hBump : Project.Runtime.takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296) (hPages : store.mem.pages ≤ 65536) :
    heap.PackedOutput store
      (write (heap.allocatePackedStore store need)
        (allocatedRoot heap.top need heap.nodes).toNat bytes) need bytes := by
  have hBounds := PackedAllocation.root_bounds store heap.top need heap.nodes hHeap.freeList
    (fun h => (hBump h).le)
  apply heap.packedOutput store _ need bytes hHeap hNeed hBump hPages (writesRange ..)
  apply represented
  · change (PackedAllocation.root heap.top need heap.nodes).toNat + bytes.size ≤ 2^32
    omega
  · change (PackedAllocation.root heap.top need heap.nodes).toNat + bytes.size ≤
      (PackedAllocation.allocated store heap.top need heap.nodes).mem.pages * 65536
    omega

#print axioms allocated

end Project.ProofKit.PackedInput
