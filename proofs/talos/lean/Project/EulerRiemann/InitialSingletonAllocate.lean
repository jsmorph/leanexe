import Project.EulerRiemann.InitialSingletonData
import Project.EulerRiemann.HeapGridBounds

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime

def initialSingletonAllocatedFrame (params saved : List Value) (base previous : UInt64) : Locals :=
  FixedArraySearch.frame params saved [] 64 previous 0 (base + 48 + 64)
    ((base + 48 + 64 - 1) / 65536 + 1) (base + 48)

def initialSingletonFinalStore (store : Store Unit) (heap : Heap) (cell : Traversal.Cell) : Store Unit :=
  initialSingletonStore (heap.allocateStore store 64) (heap.top + 48) cell

theorem initial_singleton_allocate_data_shape : (initialCellsBody.drop 45).take 119 =
    FixedArrayAllocateNone.program 31 initialSingletonFit 7 ++ (initialCellsBody.drop 60).take 104 := rfl

theorem initial_singleton_allocate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved : List Value) (hParams : params.length = 1) (hSaved : saved.length = 30)
    (previous current capacity next result : UInt64) (cell : Traversal.Cell)
    (hHeap : heap.At store) (hNone : takeFirstFitFrom 0 64 heap.nodes = none)
    (hFit32 : heap.top.toNat + 48 + 64 < 4294967296) (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top 64 ≤ store.memoryCap module 0)
    (hData : ∀ field : Nat, field < 7 →
      (FixedArraySearch.frame params saved [] 64 previous current capacity next result).get (6 + field) =
        some (.i64 ((Memory.cellWords cell).getD field 0)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previousAfter,
      (heap.allocate 64).At (initialSingletonFinalStore store heap cell) →
      (heap.allocate 64).Owns (initialSingletonFinalStore store heap cell)
        (allocatedNode heap.top 64 heap.nodes) #[cell] →
      Memory.WritesGrid (heap.allocateStore store 64) (initialSingletonFinalStore store heap cell)
        (heap.top + 48) 1 →
      wp module rest Q (initialSingletonFinalStore store heap cell)
        (initialSingletonDataFrame (initialSingletonAllocatedFrame params saved heap.top previousAfter)
          (heap.top + 48) cell) env) :
    wp module ((initialCellsBody.drop 45).take 119 ++ rest) Q store
      (FixedArraySearch.frame params saved [] 64 previous current capacity next result) env := by
  have hBasic : takeFirstFit 64 heap.nodes = none := by
    rw [← takeFirstFitFrom_project 0 64 heap.nodes, hNone]
    rfl
  have hBounds := heap.allocate_grid_bounds store 64 1 hHeap (by decide) (fun _ => hFit32.le)
  simp only [allocatedRoot, hNone, Nat.reduceMul, Nat.reduceAdd] at hBounds
  rw [initial_singleton_allocate_data_shape, List.append_assoc]
  apply FixedArrayAllocateNone.program_spec module env store params saved [] 31 (by omega)
    initialSingletonFit heap.top 64 7 previous current capacity next result heap.allocations heap.nodes
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hBasic hFit32.le hPages rfl hCap
  intro previousAfter
  rw [← initial_allocateStore_eq heap store 64 hNone]
  let frame := initialSingletonAllocatedFrame params saved heap.top previousAfter
  have hRoot : frame.get 36 = some (.i64 (heap.top + 48)) := by
    have h := FixedArraySearch.frame_get params saved [] 64 previousAfter 0 (heap.top + 48 + 64)
      ((heap.top + 48 + 64 - 1) / 65536 + 1) (heap.top + 48) 5 (by decide)
    simpa [frame, initialSingletonAllocatedFrame, hParams, hSaved] using h
  have hFields (field : Nat) (hf : field < 7) :
      frame.get (6 + field) = some (.i64 ((Memory.cellWords cell).getD field 0)) := by
    have hBefore : 6 + field < params.length + saved.length := by omega
    dsimp only [frame, initialSingletonAllocatedFrame]
    rw [FixedArraySearch.frame_get_before params saved [] 64 previousAfter 0 (heap.top + 48 + 64)
      ((heap.top + 48 + 64 - 1) / 65536 + 1) (heap.top + 48) (6 + field) hBefore]
    rw [← FixedArraySearch.frame_get_before params saved [] 64 previous current capacity next result
      (6 + field) hBefore]
    exact hData field hf
  apply initial_singleton_data_spec env (heap.allocateStore store 64) frame (heap.top + 48) cell
    hParams (by simp [frame, initialSingletonAllocatedFrame, FixedArraySearch.frame, hSaved])
    rfl hRoot hFields hBounds.1 hBounds.2
  intro hGrid hWrites
  have hFinished := heap.finishGrid store (initialSingletonFinalStore store heap cell) 64 #[cell]
    hHeap (by simp) (fun _ => hFit32)
    (by simpa [allocatedRoot, hNone, initialSingletonFinalStore] using hWrites)
    (by simpa [allocatedRoot, hNone, initialSingletonFinalStore] using hGrid)
  exact hNext previousAfter hFinished.1 hFinished.2 hWrites

#print axioms initial_singleton_allocate_data_shape
#print axioms initial_singleton_allocate_spec

end Project.EulerRiemann.Execution
