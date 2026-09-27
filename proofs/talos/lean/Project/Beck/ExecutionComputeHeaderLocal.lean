import Project.Beck.ExecutionComputeHeader

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computeHeaderLocal_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer overlap : UInt64) (locals : List Value) (size : locals.length = 79) (typed : WordLocals locals)
    (overlapRead : locals[11]? = some (.i64 overlap)) (remaining pageLimit : Nat)
    (valid : heap.At initial) (budget : OutputBudget initial heap (72 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : let final := pairWords heap initial 0 overlap
      let node := allocatedNode heap.top 24 heap.nodes
      (heap.allocate 24).At final → (heap.allocate 24).OwnsWords final node #[0, overlap] →
      heap.Frame initial (heap.allocate 24) final → FreshFor heap node →
      OutputBudget final (heap.allocate 24) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 35 31 →
      nextLocals[35]? = some (.i64 node.root) → nextLocals[36]? = some (.i64 node.root) →
      Q (.Fallthrough final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» (computeOutput.take 71) Q initial { params := [.i64 pointer], locals := locals } env := by
  obtain ⟨need, previous, current, capacity, afterNode, result, frameEq⟩ :=
    typed.allocationFrame [.i64 pointer] 60 (by omega)
  have savedSize : (locals.take 60).length = 60 := by simp [List.length_take, size]
  have tailSize : (locals.drop 66).length = 13 := by simp [size]
  rw [frameEq]
  simpa only [List.append_nil] using computeHeader_exact env initial heap pointer (locals.take 60) (locals.drop 66)
    savedSize tailSize need previous current capacity afterNode result overlap (by simpa using overlapRead)
    remaining pageLimit valid budget Q [] (by
      dsimp only
      intro finalValid owned preserved fresh finalBudget previous current capacity afterNode
      rw [wp_nil]
      apply next finalValid owned preserved fresh finalBudget
      · have windowTyped : WordLocals [.i64 24, .i64 previous, .i64 current, .i64 capacity, .i64 afterNode,
            .i64 (allocatedRoot heap.top 24 heap.nodes)] := by
          repeat' apply WordLocals.cons
          exact WordLocals.nil
        have update := wordWindow_update locals _ 60 typed windowTyped (by simp [size])
        have changed := ((((update.widen 35 31 (by decide) (by simp)).set 56 (allocatedRoot heap.top 24 heap.nodes)
          (by decide) (by decide)).set 59 overlap (by decide) (by decide)).set 35 (allocatedRoot heap.top 24 heap.nodes)
          (by decide) (by decide)).set 36 (allocatedRoot heap.top 24 heap.nodes) (by decide) (by decide)
        simpa [FixedArraySearch.frame, List.set_append, savedSize, List.length_set, allocatedNode] using changed
      · simp [FixedArraySearch.frame, List.getElem?_append, savedSize, allocatedNode]
      · simp [FixedArraySearch.frame, List.getElem?_append, savedSize, allocatedNode])

#print axioms computeHeaderLocal_exact

end Project.Beck.Execution
