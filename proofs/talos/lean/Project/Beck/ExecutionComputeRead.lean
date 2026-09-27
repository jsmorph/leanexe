import Project.Beck.ExecutionComputeState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeRead_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (words : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (represented : UInt64Array.At initial pointer words)
    (wordsProtected : heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)))
    (accepted : (readInput words).status = 0)
    (budget : OutputBudget initial heap (112 + 1520 * words[0]!.toNat + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node owner, finalHeap.At final →
      finalHeap.OwnsWords final node (readInput words).incidence → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ((readInput words).jobs = 0 ∨ owner = node.root) →
      ∀ locals, ComputeInputLocals locals (readInput words) owner node.root →
      Q (.Fallthrough final { params := [.i64 pointer], locals := locals })) :
    wp Project.Beck.«module» (func35.take 25) Q initial
      { params := [.i64 pointer], locals := List.replicate 79 (.i64 0) } env := by
  have call := readInput_owner_exact (wordsOwner := 0) env initial heap pointer words remaining pageLimit
    valid represented wordsProtected (Or.inl rfl) accepted budget
  simp only [func35, List.take]
  wp_fixed_frame
  apply wp_call_tw call
  rintro final values ⟨finalHeap, node, owner, rfl, finalValid, owned, preserved, finalBudget, ownerEq⟩
  simp only [inputValues]
  wp_fixed_frame
  apply next final finalHeap node owner finalValid owned preserved finalBudget ownerEq
  constructor
  · rfl
  · repeat' apply WordLocals.cons
    exact WordLocals.nil
  all_goals rfl

#print axioms computeRead_exact

end Project.Beck.Execution
