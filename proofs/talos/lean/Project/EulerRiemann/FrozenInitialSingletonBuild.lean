import Project.EulerRiemann.FrozenInitialSingletonPrefix

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime

def initialSingletonBuiltFrame (n : Nat) (base previous : UInt64) : Locals :=
  initialSingletonDataFrame
    (initialSingletonAllocatedFrame [.i64 (UInt64.ofNat n)] (initialSingletonSaved n) base previous)
    (base + 48) (Traversal.initialCell n 0)

theorem initial_singleton_build_shape : initialCellsBody.take 164 =
    initialCellsBody.take 45 ++ (initialCellsBody.drop 45).take 119 := rfl

theorem initial_singleton_build_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (n : Nat) (hn : n ≤ 800) (hHeap : heap.At store)
    (hNone : takeFirstFitFrom 0 64 heap.nodes = none)
    (hFit32 : heap.top.toNat + 48 + 64 < 4294967296) (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top 64 ≤ store.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previousAfter,
      (heap.allocate 64).At (initialSingletonFinalStore store heap (Traversal.initialCell n 0)) →
      (heap.allocate 64).Owns (initialSingletonFinalStore store heap (Traversal.initialCell n 0))
        (allocatedNode heap.top 64 heap.nodes) #[Traversal.initialCell n 0] →
      Memory.WritesGrid (heap.allocateStore store 64)
        (initialSingletonFinalStore store heap (Traversal.initialCell n 0)) (heap.top + 48) 1 →
      wp module rest Q (initialSingletonFinalStore store heap (Traversal.initialCell n 0))
        (initialSingletonBuiltFrame n heap.top previousAfter) env) :
    wp module (initialCellsBody.take 164 ++ rest) Q store (initialCellsEntryFrame n) env := by
  rw [initial_singleton_build_shape, List.append_assoc]
  apply initial_singleton_prefix_spec env store n hn
  exact initial_singleton_allocate_spec env store heap [.i64 (UInt64.ofNat n)] (initialSingletonSaved n)
    rfl (initial_singleton_saved_length n) 0 0 0 0 0 (Traversal.initialCell n 0)
    hHeap hNone hFit32 hPages hCap (initial_singleton_prepared_data n) Q rest hNext

#print axioms initial_singleton_build_shape
#print axioms initial_singleton_build_spec

end Project.EulerRiemann.Frozen.Execution
