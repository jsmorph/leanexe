import Project.Beck.ExecutionDirectionZero
import Project.Beck.ExecutionDirectionFirstSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem directionZeroLocals_update (locals : List Value) (typed : WordLocals locals) (size : locals.length = 112)
    (jobs : Nat) (root previous current capacity afterNode : UInt64) :
    WordUpdate locals (directionZeroLocals locals jobs root previous current capacity afterNode) 48 56 := by
  refine ⟨(directionZeroLocals_size locals size jobs root previous current capacity afterNode).trans size.symm,
    directionZeroLocals_words typed jobs root previous current capacity afterNode, ?_⟩
  intro index outside
  rcases outside with before | after
  · exact directionZeroLocals_keeps locals size jobs root previous current capacity afterNode index before
  · unfold directionZeroLocals
    rw [List.getElem?_append_right (by simp [directionZeroPrepared, size]; omega)]
    simp only [List.length_append, List.length_set, List.length_take, directionZeroPrepared, size,
      List.length_cons, List.length_nil, Nat.reduceAdd, List.getElem?_drop]
    have position : 101 + (index - (min 95 112 + 6)) = index := by omega
    rw [position]
    simp (discharger := omega) only [List.getElem?_set_ne]

set_option maxRecDepth 4096 in
theorem direction_vector_shape : directionEligible.take 66 =
    directionEligible.take 48 ++ (directionEligible.drop 48).take 18 := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionVector_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer value : UInt64) (free : Nat)
    (localsSize : locals.length = 112) (typed : WordLocals locals) (jobsBound : input.jobs ≤ 6) (inside : free < input.jobs)
    (freeRead : locals[46]? = some (.i64 free.toUInt64)) (valueRead : locals[33]? = some (.i64 value))
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (budget : OutputBudget initial heap (2 * (48 + 8 * (input.jobs + 1)) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final →
      finalHeap.OwnsWords final node ((Array.replicate input.jobs 0).set! free value) →
      heap.Frame initial finalHeap final → FreshFor heap node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 48 56 →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
          locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» (directionEligible.take 66) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let bytes := 48 + 8 * (input.jobs + 1)
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  rw [direction_vector_shape]
  apply Sequence.wp_append (P := fun store frame => ∃ middle previous current capacity afterNode,
    let node := allocatedNode heap.top (UInt64.ofNat (8 * (input.jobs + 1))) heap.nodes
    middle.At store ∧ middle.OwnsWords store node (Array.replicate input.jobs 0) ∧
    heap.Frame initial middle store ∧ OutputBudget store middle (bytes + remaining) pageLimit Project.Beck.«module» ∧
    frame = { params := params, locals := directionZeroLocals locals input.jobs node.root previous current capacity afterNode })
  · apply directionZero_exact env initial heap locals input point inputOwner inputPointer pointOwner pointPointer localsSize typed jobsBound
      (bytes + remaining) pageLimit valid
    · simpa only [bytes, Nat.two_mul, Nat.add_assoc] using budget
    · intro final
      dsimp only
      intro finalValid owned preserved _ finalBudget previous current capacity afterNode
      exact ⟨_, previous, current, capacity, afterNode, finalValid, owned, preserved, finalBudget, rfl⟩
  rintro middleStore frame ⟨middle, previous, current, capacity, afterNode, middleValid, owned, preserved, middleBudget, frameSame⟩
  subst frame
  let node := allocatedNode heap.top (UInt64.ofNat (8 * (input.jobs + 1))) heap.nodes
  let prepared := directionZeroLocals locals input.jobs node.root previous current capacity afterNode
  have update : WordUpdate locals prepared 48 56 := directionZeroLocals_update locals typed localsSize input.jobs node.root previous current capacity afterNode
  have preparedSize : prepared.length = 112 := update.size.trans localsSize
  apply directionFirstSet_exact env middleStore middle params prepared update.words paramsSize preparedSize node.root value
    (Array.replicate input.jobs 0) free
  · simp [prepared, directionZeroLocals, directionZeroPrepared, localsSize]
  · exact (update.keeps 46 (Or.inl (by omega))).trans freeRead
  · exact (update.keeps 33 (Or.inl (by omega))).trans valueRead
  · exact middleValid
  · simpa using (show input.jobs ≤ 56 by omega)
  · simpa using inside
  · exact owned.buffer.values
  · exact ownedWords_protects owned
  · simpa only [Array.size_replicate] using middleBudget
  · intro final
    dsimp only
    intro finalValid result finalFrame fresh finalBudget nextLocals changed
    exact next final _ _ finalValid result (preserved.trans finalFrame) (fresh.original preserved) finalBudget nextLocals
      (update.trans (changed.widen 48 56 (by omega) (by omega)))

#print axioms directionVector_exact

end Project.Beck.Execution
