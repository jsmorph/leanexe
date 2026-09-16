import Project.EulerCertificate.SolverRegion
import Project.EulerReconstructed.SweepPageBound
import Project.EulerReconstructed.RetainedMemory
import Project.EulerReconstructed.GridScan

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution

theorem sweep_pages_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel : UInt64) (axis : Bool) (ratio : UInt64)
    (pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
      bumpPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerCertificate.«module» 0)
    (hBumpPages : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (normalizedCapacity (UInt64.ofNat grid.size) 7).toNat ≤
        pageLimit * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let node := allocatedNode heap.top need heap.nodes
    TerminatesWith env Project.EulerCertificate.«module» 159 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 (boolWord axis), .i64 fuel, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 node.root, .i64 node.root] ∧
        (heap.allocate need).At final ∧
        (heap.allocate need).Owns final source grid ∧
        (heap.allocate need).Owns final node (Project.EulerReconstructed.Traversal.sweep n fuel.toNat axis ratio grid) ∧
        regionsDisjoint source.region node.region ∧
        final.mem.pages ≤ pageLimit ∧
        final.memoryCap Project.EulerCertificate.«module» 0 = initial.memoryCap Project.EulerCertificate.«module» 0 ∧
        Memory.WritesGrid (heap.allocateStore initial need) final node.root grid.size) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 121 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.sweep_pages_owned env initial heap source grid n fuel axis ratio
      pageLimit hn hIndexed hHeap hOwner hPages hPageLimit hBump hBumpPages)

theorem initial_cells_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (n limit pageLimit : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 800)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hReserve : heap.top.toNat + 112 + initialRemainingBytes 1 20 (n * n) ≤ limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerCertificate.«module» 0 * 65536)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hPhysicalLimit : limit ≤ pageLimit * 65536) :
    TerminatesWith env Project.EulerCertificate.«module» 53 initial [.i64 (UInt64.ofNat n)]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root] ∧
        RetryStoreAt initial heap final finalHeap ∧
        finalHeap.Owns final result (Traversal.initialCells n) ∧
        result.capacity.toNat = initialBytes (n * n) ∧ finalHeap.top.toNat ≤ limit ∧
        final.mem.pages ≤ pageLimit ∧
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region)) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 141 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.initial_cells_exact env initial heap n limit pageLimit hn2 hn hHeap hBelow hReserve hLimit hCap hPages hPageLimit hPhysicalLimit)

theorem output_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n pageLimit : Nat) (time status : UInt64)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid) (hSize : grid.size ≤ 640000)
    (hBudget : OutputBudget initial heap (outputBytes grid.size) pageLimit) :
    TerminatesWith env Project.EulerCertificate.«module» 3 initial
      [.i64 source.root, .i64 source.root, .i64 status, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root, .i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Output.pack n time status grid) ∧ final.mem.pages ≤ pageLimit) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 144 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.output_exact env initial heap source grid n pageLimit time status hHeap hOwner hSize hBudget)

theorem release_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (grid : Array Traversal.Cell)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial node grid) :
    TerminatesWith env Project.EulerCertificate.«module» 194 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 152 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.release_owned env initial heap node grid hHeap hOwner)

theorem scan_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 89 initial [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (OutwardMaximum.gridUpper grid).value, .i64 (OutwardMaximum.gridUpper grid).status]) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 46 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.scan_exact env initial owner pointer grid hGrid)

#print axioms sweep_pages_owned
#print axioms initial_cells_exact
#print axioms output_exact
#print axioms release_owned
#print axioms scan_exact
end Project.EulerCertificate.Execution
