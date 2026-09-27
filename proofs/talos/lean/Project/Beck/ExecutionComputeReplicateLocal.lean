import Project.Beck.ExecutionComputeReplicate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeReplicateLocal_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (locals : List Value) (size : locals.length = 79) (typed : WordLocals locals)
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
      ∀ nextLocals, WordUpdate locals nextLocals 57 11 → nextLocals[57]? = some (.i64 node.root) →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» ((computeAccepted.drop 22).take 42) Q initial
      { params := [.i64 pointer], locals := locals } env := by
  obtain ⟨need, previous, current, capacity, afterNode, result, frameEq⟩ :=
    typed.allocationFrame [.i64 pointer] 62 (by omega)
  have savedSize : (locals.take 62).length = 62 := by simp [List.length_take, size]
  have tailSize : (locals.drop 68).length = 11 := by simp [size]
  rw [frameEq]
  simpa only [List.append_nil] using computeReplicate_exact env initial heap [.i64 pointer] (locals.take 62) (locals.drop 68)
    rfl savedSize tailSize need previous current capacity afterNode result jobs remaining pageLimit jobsBound
    (by simpa using lengthRead) (by simpa using valueRead) valid budget Q [] (by
      intro final
      dsimp only
      intro finalValid owned preserved fresh finalBudget previous current capacity afterNode
      rw [wp_nil]
      apply next final finalValid owned preserved fresh finalBudget
      · have windowTyped : WordLocals
            [.i64 (UInt64.ofNat (8 * (jobs + 1))), .i64 previous, .i64 current, .i64 capacity, .i64 afterNode,
              .i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (jobs + 1))) heap.nodes)] := by
          repeat' apply WordLocals.cons
          exact WordLocals.nil
        have update := wordWindow_update locals _ 62 typed windowTyped (by simpa [size])
        have updated := ((update.widen 57 11 (by decide) (by simp)).set 57
          (allocatedRoot heap.top (UInt64.ofNat (8 * (jobs + 1))) heap.nodes) (by decide) (by decide)).set 58
            jobs.toUInt64 (by decide) (by decide)
        simpa [FixedArraySearch.frame, List.set_append, savedSize, List.length_set, allocatedNode] using updated
      · simp [FixedArraySearch.frame, List.getElem?_append, savedSize, List.getElem?_set, allocatedNode])

#print axioms computeReplicateLocal_exact

end Project.Beck.Execution
