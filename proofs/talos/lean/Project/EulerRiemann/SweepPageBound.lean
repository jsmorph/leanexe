import Project.EulerRiemann.SweepOwned
import Project.EulerRiemann.AllocationPageBound

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem sweep_pages_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (axis : Bool) (ratio : UInt64)
    (pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
      bumpPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerRiemann.«module» 0)
    (hBumpPages : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (normalizedCapacity (UInt64.ofNat grid.size) 7).toNat ≤
        pageLimit * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let node := allocatedNode heap.top need heap.nodes
    TerminatesWith env Project.EulerRiemann.«module» 77 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 (boolWord axis), .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).Owns final source grid ∧
        (heap.allocate need).Owns final node (Traversal.sweep n axis ratio grid) ∧
        regionsDisjoint source.region node.region ∧
        final.mem.pages ≤ pageLimit ∧
        final.memoryCap Project.EulerRiemann.«module» 0 = initial.memoryCap Project.EulerRiemann.«module» 0 ∧
        Memory.WritesGrid (heap.allocateStore initial need) final node.root grid.size) := by
  apply (sweep_owned env initial heap source grid n axis ratio hn hIndexed hHeap hOwner
    (hPages.trans hPageLimit) hBump).mono
  rintro final values ⟨hValues, hHeapFinal, hSource, hResult, hSeparated, _, hCap, hWrites⟩
  exact ⟨hValues, hHeapFinal, hSource, hResult, hSeparated,
    allocated_grid_pages_bound heap initial final _ _ _ pageLimit hPages hBumpPages hWrites,
    hCap, hWrites⟩

#print axioms sweep_pages_owned

end Project.EulerRiemann.Execution
