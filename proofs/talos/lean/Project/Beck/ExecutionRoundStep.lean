import Project.Beck.ExecutionRoundAdvance

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem round_step_shape : roundBody.drop 4 = (roundBody.drop 4).take 101 ++
    ((roundBody.drop 105).take 13 ++ (loopArrayCleanupProgram 45 84 82 ++ roundBody.drop 130)) := rfl

set_option maxRecDepth 4096 in
theorem roundStep_exact (env : HostEnv Unit) (initial middle : Store Unit) (originalHeap heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (d words : Array UInt64) (currentNode : FreeNode)
    (inputOwner inputPointer pointOwner pointPointer directionRoot distance speed denominator original : UInt64)
    (index remaining pageLimit : Nat)
    (state : RoundLoopLocals locals directionRoot distance speed denominator original currentNode.root index input.jobs)
    (valid : heap.At middle) (owned : heap.OwnsWords middle currentNode words)
    (preserved : originalHeap.Frame initial heap middle) (active : currentNode.root = original ∨ FreshFor originalHeap currentNode)
    (capacity : input.jobs ≤ 6) (inside : index < input.jobs) (wordsBound : words.size ≤ 5)
    (pointAt : UInt64Array.At middle pointPointer point.numerators) (directionAt : UInt64Array.At middle directionRoot d)
    (pointSize : input.jobs ≤ point.numerators.size) (directionSize : input.jobs ≤ d.size)
    (budget : OutputBudget middle heap (104 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode
        (words.push (point.numerators[index] * speed + distance * d[index])) →
      originalHeap.Frame initial finalHeap final → FreshFor originalHeap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, RoundLoopLocals nextLocals directionRoot distance speed denominator original resultNode.root (index + 1) input.jobs →
      Q (.Break 0 final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := nextLocals })) :
    wp Project.Beck.«module» (roundBody.drop 4) Q middle
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  rw [round_step_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((roundBody.drop 105).take 13 ++ (loopArrayCleanupProgram 45 84 82 ++ roundBody.drop 130)) Q store frame env) ?_ (fun _ _ h => h)
  apply roundAppend_exact env middle heap locals input point d words
    inputOwner inputPointer pointOwner pointPointer directionRoot distance speed denominator original currentNode.root index remaining pageLimit
    state valid (by omega) pointAt directionAt (inside.trans_le pointSize) (inside.trans_le directionSize)
    owned.buffer.values (ownedWords_protects owned) (budget.mono (by omega))
  intro calcStore
  dsimp only
  intro calcValid resultOwned calcFrame fresh calcBudget calcLocals calcState
  dsimp only [Sequence.Fallthrough]
  let calcHeap := heap.allocate (UInt64.ofNat (8 * (words.size + 2)))
  let resultNode := allocatedNode heap.top (UInt64.ofNat (8 * (words.size + 2))) heap.nodes
  let ready := roundResultLocals calcLocals resultNode.root
  have readyState := roundResult_state calcState resultNode.root
  have readySize : ready.length = 77 := readyState.size
  refine Sequence.wp_append (P := fun store frame => store = calcStore ∧ frame = { params := params, locals := ready }) ?_ ?_
  · exact roundResult_exact env calcStore params calcLocals resultNode.root paramsSize calcState.size _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply loopArrayCleanup_exact env initial calcStore originalHeap calcHeap { params := params, locals := ready }
    45 84 82 currentNode resultNode words (words.push (point.numerators[index] * speed + distance * d[index])) original
    remaining pageLimit calcValid (calcFrame.ownsWords calcValid owned) resultOwned (preserved.trans calcFrame) active
    (fresh.separated owned resultOwned.buffer.rootBound) calcBudget rfl
  · simpa only [Locals.get, paramsSize, readySize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using readyState.currentOwner
  · simpa only [Locals.get, paramsSize, readySize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using readyState.originalOwner
  · simp [Locals.get, paramsSize, ready, roundResultLocals, calcState.size]
  · intro final finalHeap finalValid finalOwned finalFrame finalBudget
    apply roundAdvance_exact env final params ready resultNode.root index (inside.trans_le capacity) paramsSize readySize
    · simp [ready, roundResultLocals, calcState.size]
    · simp [ready, roundResultLocals, calcState.size]
    · simp [ready, roundResultLocals, calcState.size]
    · exact readyState.position
    · exact readyState.step
    · exact next final finalHeap resultNode finalValid finalOwned finalFrame (fresh.original preserved) finalBudget _
        (roundAdvance_state readyState resultNode.root)

#print axioms roundStep_exact

end Project.Beck.Execution
