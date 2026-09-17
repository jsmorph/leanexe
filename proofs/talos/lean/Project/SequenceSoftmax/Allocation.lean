import Project.EulerRiemann.HeapWordsFinish
import Project.EulerRiemann.WordAllocationBounds
import Project.ProofKit.UInt64ArrayAllocation

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
  UInt64Array ProofKit.Memory

abbrev mapCapacity := UInt64ArrayAllocation.capacity

def mapRoot (heap : Heap) (size : Nat) : UInt64 :=
  allocatedRoot heap.top (mapCapacity size) heap.nodes

def mapAllocated (heap : Heap) (initial : Store Unit) (size : Nat) : Store Unit :=
  heap.allocateArrayStore initial (mapCapacity size) 1

def mapInitialized (heap : Heap) (initial : Store Unit) (size : Nat) : Store Unit :=
  FixedArrayResult.writeLength (mapAllocated heap initial size) (mapRoot heap size) (UInt64.ofNat size)

theorem map_capacity (initial : Store Unit) (ptr : UInt64) (input : Array UInt64)
    (hInput : At initial ptr input) :
    (mapCapacity input.size).toNat = 8*(input.size+1) ∧
      FixedArrayCapacity.normalizedCapacity (UInt64.ofNat input.size) 1 = mapCapacity input.size := by
  have hFit := hInput.1
  have hSize : (UInt64.ofNat input.size).toNat = input.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  have hCapacity : (mapCapacity input.size).toNat = 8*(input.size+1) :=
    UInt64.toNat_ofNat_of_lt' (by change 8*(input.size+1) < 18446744073709551616; omega)
  refine ⟨hCapacity, UInt64.toNat_inj.mp ?_⟩
  rw [FixedArrayCapacity.normalizedCapacity_toNat_of_fits (UInt64.ofNat input.size) 1
    (by rw [hSize]; change 8+input.size*1*8+7 < 18446744073709551616; omega), hCapacity, hSize]
  change 8+input.size*1*8 = 8*(input.size+1)
  omega

theorem map_initialize (heap : Heap) (initial : Store Unit) (source : FreeNode)
    (input output : Array UInt64) (hHeap : heap.At initial)
    (hInput : heap.OwnsWords initial source input) (hSize : output.size = input.size)
    (hBump : takeFirstFitFrom 0 (mapCapacity input.size) heap.nodes = none →
      heap.top.toNat+48+(mapCapacity input.size).toNat ≤ 4294967296) :
    PrefixAt (mapInitialized heap initial input.size) (mapRoot heap input.size) output 0 ∧
    At (mapInitialized heap initial input.size) source.root input ∧
    (source.root.toNat+8*(input.size+1) ≤ (mapRoot heap input.size).toNat ∨
      (mapRoot heap input.size).toNat+8*(input.size+1) ≤ source.root.toNat) ∧
    WritesRange (mapAllocated heap initial input.size) (mapInitialized heap initial input.size)
      (mapRoot heap input.size).toNat ((mapRoot heap input.size).toNat+8*(input.size+1)) := by
  have hNeed := (map_capacity initial source.root input hInput.buffer.values).1
  have hBounds := heap.allocate_word_bounds initial (mapCapacity input.size) 1 input.size
    hHeap (by omega) hBump
  change (mapRoot heap input.size).toNat+8*(input.size+1) ≤ 4294967296 ∧
    (mapRoot heap input.size).toNat+8*(input.size+1) ≤
      (mapAllocated heap initial input.size).mem.pages*65536 at hBounds
  have hAddress : (mapRoot heap input.size).toUInt32.toNat = (mapRoot heap input.size).toNat := by
    rw [ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by change (mapRoot heap input.size).toNat < 4294967296; omega)]
  have hWrites : WritesRange (mapAllocated heap initial input.size)
      (mapInitialized heap initial input.size) (mapRoot heap input.size).toNat
      ((mapRoot heap input.size).toNat+8*(input.size+1)) :=
    WritesRange.write64 _ _ _ _ _ (by rw [hAddress]) (by rw [hAddress]; omega)
  have hDisjoint := hInput.allocate_word_disjoint (mapCapacity input.size) input.size (by omega) hBump
  have hAllocatedInput := (hInput.arrayAllocated (mapCapacity input.size) 1 hHeap hBump).buffer.values
  refine ⟨?_, hAllocatedInput.writesRange hWrites hDisjoint, hDisjoint, hWrites⟩
  apply PrefixAt.empty
  · simpa only [hSize] using hBounds.1
  · simpa only [mapInitialized, FixedArrayResult.writeLength_pages, hSize] using hBounds.2
  · simpa only [mapInitialized, FixedArrayResult.writeLength, hSize] using
      (ProofKit.Memory.read64_write64 (mapAllocated heap initial input.size).mem
        (mapRoot heap input.size).toUInt32 (UInt64.ofNat input.size))

#print axioms map_capacity
#print axioms map_initialize
end Project.SequenceSoftmax.Spec
