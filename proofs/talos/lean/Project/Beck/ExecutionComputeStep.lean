import Project.Beck.ExecutionComputeAdvance
import Project.Beck.ExecutionDirectionSeed

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem compute_step_shape : computeOutputBody.drop 4 = (computeOutputBody.drop 4).take 98 ++
    ((computeOutputBody.drop 102).take 13 ++ (loopArrayCleanupProgram 38 78 76 ++ computeOutputBody.drop 127)) := rfl

set_option maxRecDepth 4096 in
theorem computeStep_exact (env : HostEnv Unit) (initial middle : Store Unit) (originalHeap heap : Heap) (locals : List Value)
    (pointer : UInt64) (input : Input) (point : Point) (words : Array UInt64) (currentNode : FreeNode)
    (initialOwner initialPointer pointRoot original : UInt64) (index remaining pageLimit : Nat)
    (state : ComputeOutputLocals locals input.jobs input.overlap initialOwner initialPointer pointRoot original currentNode.root index)
    (valid : heap.At middle) (owned : heap.OwnsWords middle currentNode words)
    (preserved : originalHeap.Frame initial heap middle) (active : currentNode.root = original ∨ FreshFor originalHeap currentNode)
    (capacity : input.jobs ≤ 6) (inside : index < input.jobs) (wordsBound : words.size ≤ 7)
    (pointAt : UInt64Array.At middle pointRoot point.numerators) (pointSize : input.jobs ≤ point.numerators.size)
    (budget : OutputBudget middle heap (120 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode (words.push (Project.Beck.Result.group point index)) →
      originalHeap.Frame initial finalHeap final → FreshFor originalHeap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, ComputeOutputLocals nextLocals input.jobs input.overlap initialOwner initialPointer pointRoot original resultNode.root (index + 1) →
      Q (.Break 0 final { params := [.i64 pointer], locals := nextLocals })) :
    wp Project.Beck.«module» (computeOutputBody.drop 4) Q middle { params := [.i64 pointer], locals := locals } env := by
  rw [compute_step_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((computeOutputBody.drop 102).take 13 ++ (loopArrayCleanupProgram 38 78 76 ++ computeOutputBody.drop 127)) Q store frame env)
    ?_ (fun _ _ h => h)
  apply computeAppend_exact env middle heap locals pointer input point words initialOwner initialPointer pointRoot original currentNode.root
    index remaining pageLimit state valid (by omega) pointAt (inside.trans_le pointSize) owned.buffer.values
    (ownedWords_protects owned) (budget.mono (by omega))
  intro calcStore
  dsimp only
  intro calcValid resultOwned calcFrame fresh calcBudget calcLocals calcState
  dsimp only [Sequence.Fallthrough]
  let calcHeap := heap.allocate (UInt64.ofNat (8 * (words.size + 2)))
  let resultNode := allocatedNode heap.top (UInt64.ofNat (8 * (words.size + 2))) heap.nodes
  let ready := computeResultLocals calcLocals resultNode.root
  have readyState := computeResult_state calcState resultNode.root
  have readySize : ready.length = 79 := readyState.size
  refine Sequence.wp_append (P := fun store frame => store = calcStore ∧ frame = { params := [.i64 pointer], locals := ready }) ?_ ?_
  · exact computeResult_exact env calcStore [.i64 pointer] calcLocals resultNode.root rfl calcState.size _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply loopArrayCleanup_exact env initial calcStore originalHeap calcHeap { params := [.i64 pointer], locals := ready }
    38 78 76 currentNode resultNode words (words.push (Project.Beck.Result.group point index)) original remaining pageLimit
    calcValid (calcFrame.ownsWords calcValid owned) resultOwned (preserved.trans calcFrame) active
    (fresh.separated owned resultOwned.buffer.rootBound) calcBudget rfl
  · simpa only [Locals.get, readySize, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using readyState.currentOwner
  · simpa only [Locals.get, readySize, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using readyState.originalOwner
  · simp [Locals.get, ready, computeResultLocals, calcState.size]
  · intro final finalHeap finalValid finalOwned finalFrame finalBudget
    apply computeAdvance_exact env final [.i64 pointer] ready resultNode.root index (inside.trans_le capacity) rfl readySize
    · simp [ready, computeResultLocals, calcState.size]
    · simp [ready, computeResultLocals, calcState.size]
    · simp [ready, computeResultLocals, calcState.size]
    · exact readyState.position
    · exact readyState.step
    · exact next final finalHeap resultNode finalValid finalOwned finalFrame (fresh.original preserved) finalBudget _
        (computeAdvance_state readyState resultNode.root)

#print axioms computeStep_exact

end Project.Beck.Execution
