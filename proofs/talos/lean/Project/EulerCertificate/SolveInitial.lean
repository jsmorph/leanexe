import Project.EulerCertificate.ExecutionSolve

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Wasm Project.Runtime

def initialHeap : Heap :=
  { top := 4096, nodes := [], allocations := 0, retains := 0, releases := 0, frees := 0 }

theorem initial_heap_at : initialHeap.At (module.initialStore (α := Unit)) := by
  refine ⟨rfl, .nil, ?_⟩
  simp [initialHeap]

theorem initial_heap_below : InitialFreeBelow 1 initialHeap.nodes := by
  simp [InitialFreeBelow, initialHeap]

theorem initial_memory_pages : (module.initialStore (α := Unit)).mem.pages = 16 := rfl

theorem initial_memory_cap : (module.initialStore (α := Unit)).memoryCap module 0 = 65536 := rfl

theorem solve_initial_exact (env : HostEnv Unit) (n : Nat) (trials : UInt64) (hn : 2 ≤ n ∧ n ≤ 800) :
    TerminatesWith env module 190 (module.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Solve.solve n trials.toNat) ∧ final.mem.pages ≤ 8192) := by
  apply solve_exact env _ initialHeap n trials 536870912 8192 hn initial_heap_at initial_heap_below
  · have hBytes := solve_bytes_bound n hn.2
    change 4096 + solveBytes n ≤ 536870912
    omega
  · decide
  · rw [initial_memory_pages]
    decide
  · decide
  · decide
  · rw [initial_memory_cap]
    decide

#print axioms initial_heap_at
#print axioms initial_heap_below
#print axioms initial_memory_pages
#print axioms initial_memory_cap
#print axioms solve_initial_exact

end Project.EulerCertificate.Execution
