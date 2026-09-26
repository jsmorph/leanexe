import Project.EulerReconstructed.FrozenRiemannRegion
import Project.EulerRiemann.FrozenExecutionInitialCells
import Project.EulerRiemann.FrozenExecutionOutput

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.Runtime
open Project.EulerRiemann.Frozen.Execution
open Project.EulerRiemann.Frozen

theorem initial_cells_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (n limit pageLimit : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 800)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hReserve : heap.top.toNat + 112 + initialRemainingBytes 1 20 (n * n) ≤ limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 * 65536)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hPhysicalLimit : limit ≤ pageLimit * 65536) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 141 initial [.i64 (UInt64.ofNat n)]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root] ∧
        RetryStoreAt initial heap final finalHeap ∧
        finalHeap.Owns final result (Traversal.initialCells n) ∧
        result.capacity.toNat = initialBytes (n * n) ∧ finalHeap.top.toNat ≤ limit ∧
        final.mem.pages ≤ pageLimit ∧
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region)) := by
  apply Project.FunctionRegion.terminatesWith RiemannRegion.shift 96
    (by norm_num [RiemannRegion.domain])
  exact Project.EulerRiemann.Frozen.Execution.initial_cells_exact env initial heap n limit pageLimit
    hn2 hn hHeap hBelow hReserve hLimit hCap hPages hPageLimit hPhysicalLimit

theorem output_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n pageLimit : Nat) (time status : UInt64)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid) (hSize : grid.size ≤ 640000)
    (hBudget : OutputBudget initial heap (outputBytes grid.size) pageLimit) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 144 initial
      [.i64 source.root, .i64 source.root, .i64 status, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root, .i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Output.pack n time status grid) ∧ final.mem.pages ≤ pageLimit) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 99
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Frozen.Execution.output_exact env initial heap source grid n pageLimit time status
      hHeap hOwner hSize hBudget)

theorem release_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (grid : Array Traversal.Cell)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial node grid) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 152 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 107
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Frozen.Execution.release_owned env initial heap node grid hHeap hOwner)

#print axioms initial_cells_exact
#print axioms output_exact
#print axioms release_owned
end Project.EulerReconstructed.Frozen.Execution
