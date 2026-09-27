import Project.EulerRiemann.InitialGrowthBounds
import Project.EulerRiemann.InitialHeapAllocation
import Project.EulerRiemann.AllocationPageBound

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity

theorem initial_requested_bytes (count : Nat) (hCount : count ≤ 1048576) :
    (normalizedCapacity (UInt64.ofNat count) 7).toNat = initialBytes count := by
  have hNat : (UInt64.ofNat count).toNat = count :=
    UInt64.toNat_ofNat_of_lt' (by change count < 18446744073709551616; omega)
  simpa only [hNat, initialBytes] using
    initial_capacity_toNat (UInt64.ofNat count) (by simpa only [hNat] using hCount)

theorem initial_no_fit (count : Nat) (hCount : count ≤ 1048576)
    (nodes : List FreeNode) (hBelow : InitialFreeBelow count nodes) :
    takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat count) 7) nodes = none :=
  Option.map_eq_none_iff.mp ((takeFirstFitFrom_project 0 _ nodes).trans
    (initialFreeBelow_none count hCount nodes hBelow))

theorem initial_allocated_top (heap : Heap) (count : Nat) (hCount : count ≤ 1048576)
    (hBelow : InitialFreeBelow count heap.nodes)
    (hFit : heap.top.toNat + 48 + initialBytes count ≤ 4294967296) :
    (heap.allocate (normalizedCapacity (UInt64.ofNat count) 7)).top.toNat =
      heap.top.toNat + 48 + initialBytes count := by
  have hNone := initial_no_fit count hCount heap.nodes hBelow
  have hNeed := initial_requested_bytes count hCount
  change (allocatedTop heap.top _ heap.nodes).toNat = _
  rw [allocatedTop_toNat _ _ _ (by intro _; simpa only [hNeed] using hFit), ite_eq_left hNone, hNeed]

theorem initial_allocated_nodes (heap : Heap) (count : Nat) (hCount : count ≤ 1048576)
    (hBelow : InitialFreeBelow count heap.nodes) :
    (heap.allocate (normalizedCapacity (UInt64.ofNat count) 7)).nodes = heap.nodes := by
  rw [initial_allocateHeap_eq heap _ (initial_no_fit count hCount heap.nodes hBelow)]

theorem initial_allocated_pages (heap : Heap) (initial final : Store Unit)
    (count pageLimit : Nat) (hCount : count ≤ 1048576) (hPages : initial.mem.pages ≤ pageLimit)
    (hFit : heap.top.toNat + 48 + initialBytes count ≤ pageLimit * 65536)
    (hWrites : Memory.WritesGrid (heap.allocateStore initial (normalizedCapacity (UInt64.ofNat count) 7))
      final (heap.top + 48) count) : final.mem.pages ≤ pageLimit := by
  apply allocated_grid_pages_bound heap initial final _ _ _ pageLimit hPages _ hWrites
  intro _
  simpa only [initial_requested_bytes count hCount] using hFit

#print axioms initial_requested_bytes
#print axioms initial_no_fit
#print axioms initial_allocated_top
#print axioms initial_allocated_nodes
#print axioms initial_allocated_pages

end Project.EulerRiemann.Execution
