import Project.Beck.ExecutionComputeReplicateLocal

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def computeArrayProgram (destination : Nat) : Wasm.Program :=
  (computeAccepted.drop 22).take 42 ++ [.localGet 58, .localSet 24, .localGet 24, .localSet destination]

set_option maxRecDepth 4096 in
theorem compute_array_shapes :
    (computeAccepted.drop 22).take 46 = computeArrayProgram 26 ∧
    (computeAccepted.drop 74).take 46 = computeArrayProgram 27 := ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeArray_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (locals : List Value) (size : locals.length = 79) (typed : WordLocals locals)
    (destination : Nat) (destinationBound : destination = 26 ∨ destination = 27)
    (jobs remaining pageLimit : Nat) (jobsBound : jobs ≤ 6)
    (lengthRead : locals[56]? = some (.i64 jobs.toUInt64)) (valueRead : locals[59]? = some (.i64 0))
    (valid : heap.At initial)
    (budget : OutputBudget initial heap (48 + 8 * (jobs + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let need := UInt64.ofNat (8 * (jobs + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (Array.replicate jobs 0) →
      heap.Frame initial (heap.allocate need) final → FreshFor heap node →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, nextLocals.length = 79 → WordLocals nextLocals →
      nextLocals[destination - 1]? = some (.i64 node.root) →
      (∀ k, k < 56 → k ≠ 23 → k + 1 ≠ destination → nextLocals[k]? = locals[k]?) →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» (computeArrayProgram destination) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  unfold computeArrayProgram
  refine Sequence.wp_append
    (P := fun store frame => wp Project.Beck.«module» [.localGet 58, .localSet 24, .localGet 24, .localSet destination]
      Q store frame env) ?_ (fun _ _ h => h)
  apply computeReplicateLocal_exact env initial heap pointer locals size typed jobs remaining pageLimit jobsBound
    lengthRead valueRead valid budget
  intro final
  dsimp only
  intro finalValid owned preserved fresh finalBudget filled update rootRead
  dsimp only [Sequence.Fallthrough]
  have filledSize : filled.length = 79 := update.size.trans size
  rcases destinationBound with rfl | rfl
  all_goals
    wp_run [filledSize, rootRead, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
    apply next final finalValid owned preserved fresh finalBudget
    · simpa only [List.length_set] using filledSize
    · exact (update.words.set 23 _).set _ _
    · simp [List.getElem?_set, filledSize, allocatedNode]
    · intro k bound first second
      simp only [List.getElem?_set, List.length_set, filledSize]
      split_ifs <;> try omega
      exact update.keeps k (Or.inl (by omega))

#print axioms computeArray_exact

end Project.Beck.Execution
