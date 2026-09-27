import Project.Beck.ExecutionRoundState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem round_append_shape : (roundBody.drop 4).take 101 = (roundBody.drop 4).take 34 ++ (roundBody.drop 38).take 67 := rfl

set_option maxRecDepth 4096 in
theorem roundAppend_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (d words : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer directionRoot distance speed denominator original current : UInt64)
    (index remaining pageLimit : Nat)
    (state : RoundLoopLocals locals directionRoot distance speed denominator original current index input.jobs)
    (valid : heap.At initial) (bound : words.size ≤ 55)
    (pointAt : UInt64Array.At initial pointPointer point.numerators) (directionAt : UInt64Array.At initial directionRoot d)
    (pointBound : index < point.numerators.size) (directionBound : index < d.size)
    (represented : UInt64Array.At initial current words)
    (protects : heap.Protects current.toNat (current.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 2))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final →
      (heap.allocate size).OwnsWords final node (words.push (point.numerators[index] * speed + distance * d[index])) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundLoopLocals nextLocals directionRoot distance speed denominator original current index input.jobs →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
          locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((roundBody.drop 4).take 101) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  let value := point.numerators[index] * speed + distance * d[index]
  let prepared := roundNumeratorLocals locals current pointPointer directionRoot index value
  have preparedState := roundNumerator_state state pointPointer value
  rw [round_append_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact roundNumerator_exact env initial locals input point d inputOwner inputPointer pointOwner pointPointer directionRoot current distance speed
      index state.size state.position state.currentPointer state.directionPointer state.distance state.speed
      pointAt directionAt pointBound directionBound _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply roundPush_exact env initial heap params prepared preparedState.words
    (by simp [params, matrixParams, inputValues, pointValues]) preparedState.size current value words
  · simp [prepared, roundNumeratorLocals, state.size]
  · simp [prepared, roundNumeratorLocals, state.size]
  · exact valid
  · exact bound
  · exact represented
  · exact protects
  · exact budget
  · intro final
    dsimp only
    intro finalValid owned preserved fresh finalBudget nextLocals changed
    exact next final finalValid owned preserved fresh finalBudget nextLocals (preparedState.updated changed)

#print axioms roundAppend_exact

end Project.Beck.Execution
