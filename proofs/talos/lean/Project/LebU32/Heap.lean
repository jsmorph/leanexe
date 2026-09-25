import Project.LebU32.Model
import Project.ProofKit.PackedPush
import Project.EulerRiemann.AllocationPageBound

namespace Project.LebU32.Spec
open Wasm Project.Common Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def byteNode (seed : Heap) (index : Nat) : FreeNode :=
  ⟨seed.top + UInt64.ofNat (48 + 56 * (index % 2)), 8⟩

def bytePointer (seed : Heap) (count : Nat) : UInt64 :=
  if count = 0 then 0 else (byteNode seed (count - 1)).root

def runningHeap (seed : Heap) (count : Nat) : Heap :=
  { top := seed.top + UInt64.ofNat (56 * min count 2)
    nodes := if count < 2 then [] else [byteNode seed count]
    allocations := seed.allocations + UInt64.ofNat count
    retains := seed.retains
    releases := seed.releases + UInt64.ofNat (count - 1)
    frees := seed.frees + UInt64.ofNat (count - 1) }

def finishedHeap (seed : Heap) (count : Nat) : Heap :=
  { top := seed.top + UInt64.ofNat (56 * min count 2)
    nodes := []
    allocations := seed.allocations + UInt64.ofNat count
    retains := seed.retains
    releases := seed.releases + UInt64.ofNat (count - 2)
    frees := seed.frees + UInt64.ofNat (count - 2) }

theorem runningHeap_zero (seed : Heap) (hNodes : seed.nodes = []) : runningHeap seed 0 = seed := by
  cases seed
  simp_all [runningHeap]

theorem byteNode_toNat (seed : Heap) (index : Nat)
    (hFit : seed.top.toNat + 112 < 4294967296) :
    (byteNode seed index).root.toNat = seed.top.toNat + 48 + 56 * (index % 2) := by
  have hMod := Nat.mod_lt index (by decide : 0 < 2)
  simp only [byteNode, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
  omega

theorem runningHeap_top (seed : Heap) (count : Nat)
    (hFit : seed.top.toNat + 112 < 4294967296) :
    (runningHeap seed count).top.toNat = seed.top.toNat + 56 * min count 2 := by
  have hMin := Nat.min_le_right count 2
  simp only [runningHeap, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
  omega

theorem byte_push_need (bytes : ByteArray) (hSize : bytes.size < 8) : PackedPush.need bytes = 8 := by
  apply UInt64.toNat.inj
  rw [PackedPush.need, PackedCapacity.capacity_toNat _ (by omega)]
  change max 8 (((bytes.size + 1 + 7) / 8) * 8) = 8
  omega

theorem running_allocate_node (seed : Heap) (count : Nat) (hCount : count ≤ 4) :
    allocatedNode (runningHeap seed count).top 8 (runningHeap seed count).nodes = byteNode seed count := by
  interval_cases count <;>
    simp [runningHeap, byteNode, allocatedNode, allocatedRoot, allocatedCapacity,
      takeFirstFitFrom, UInt64.add_assoc]

theorem running_allocate_heap (seed : Heap) (count : Nat) (hCount : count ≤ 4) :
    (runningHeap seed count).allocate 8 = finishedHeap seed (count + 1) := by
  interval_cases count <;>
    simp [runningHeap, finishedHeap, byteNode, Heap.allocate, allocatedTop, allocatedNodes,
      takeFirstFitFrom, UInt64.add_assoc]

theorem running_release_heap (seed : Heap) (count : Nat) (hCount : count ≤ 4) (hPositive : 0 < count) :
    (finishedHeap seed (count + 1)).release (byteNode seed (count - 1)) = runningHeap seed (count + 1) := by
  interval_cases count <;>
    simp_all [runningHeap, finishedHeap, byteNode, Heap.release, UInt64.add_assoc]

theorem first_heap (seed : Heap) : finishedHeap seed 1 = runningHeap seed 1 := rfl

theorem running_bump_count (seed : Heap) (count : Nat)
    (hNone : takeFirstFitFrom 0 8 (runningHeap seed count).nodes = none) : count < 2 := by
  by_contra h
  simp [runningHeap, h, takeFirstFitFrom, byteNode] at hNone

theorem running_bump_bound (seed : Heap) (count : Nat)
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hNone : takeFirstFitFrom 0 8 (runningHeap seed count).nodes = none) :
    (runningHeap seed count).top.toNat + 48 + 8 ≤ seed.top.toNat + 112 := by
  have hc := running_bump_count seed count hNone
  rw [runningHeap_top seed count hFit]
  omega

theorem running_protects_low (seed : Heap) (count : Nat)
    (hFit : seed.top.toNat + 112 < 4294967296) :
    (runningHeap seed count).Protects 0 seed.top.toNat := by
  refine ⟨?_, ?_⟩
  · rw [runningHeap_top seed count hFit]
    omega
  · intro node hNode
    simp only [runningHeap] at hNode
    split at hNode
    · simp at hNode
    · simp only [List.mem_singleton] at hNode
      subst node
      exact Or.inl (by rw [byteNode_toNat seed count hFit]; omega)

#print axioms running_allocate_node
#print axioms running_allocate_heap
#print axioms running_release_heap
#print axioms running_bump_bound
end Project.LebU32.Spec
