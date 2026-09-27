import Project.Beck.ExecutionDirectionAdvance

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem direction_step_shape : directionBody.drop 4 =
    (directionBody.drop 4).take 86 ++ ((directionBody.drop 90).take 17 ++
      ((directionBody.drop 107).take 6 ++ (loopArrayCleanupProgram 63 119 117 ++ directionBody.drop 125))) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionStep_exact (env : HostEnv Unit) (initial middle : Store Unit) (originalHeap heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (matrix words : Array UInt64) (currentNode : FreeNode)
    (inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp original : UInt64)
    (free index remaining pageLimit : Nat) (indexBound : index < basis.columns.size)
    (state : DirectionLoopLocals locals matrixPointer sro srp sco scp basis ro rp co cp original currentNode.root free index)
    (valid : heap.At middle) (owned : heap.OwnsWords middle currentNode words)
    (preserved : originalHeap.Frame initial heap middle) (active : currentNode.root = original ∨ FreshFor originalHeap currentNode)
    (wellFormed : Project.Beck.Basis.WellFormed input.jobs matrix basis)
    (widthBound : input.jobs ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size ≤ 6)
    (freeBound : free < input.jobs) (wordsSize : words.size = input.jobs)
    (matrixAt : UInt64Array.At middle matrixPointer matrix) (references : BasisReferences heap middle basis rp cp)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (budget : OutputBudget middle heap (directionCofactorBytes basis input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap resultNode, finalHeap.At final →
      finalHeap.OwnsWords final resultNode
        (words.set! basis.columns[index].toNat (0 - determinant basis.rows.size input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64))) →
      originalHeap.Frame initial finalHeap final → FreshFor originalHeap resultNode →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, DirectionLoopLocals nextLocals matrixPointer sro srp sco scp basis ro rp co cp original resultNode.root free (index + 1) →
      Q (.Break 0 final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := nextLocals })) :
    wp Project.Beck.«module» (directionBody.drop 4) Q middle
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  have indexSmall : index < 6 := by have := wellFormed.square; omega
  rw [direction_step_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((directionBody.drop 90).take 17 ++ ((directionBody.drop 107).take 6 ++
      (loopArrayCleanupProgram 63 119 117 ++ directionBody.drop 125))) Q store frame env) ?_ (fun _ _ h => h)
  apply directionCofactor_exact env middle heap locals input point basis matrix words
    inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp original currentNode.root
    free index remaining pageLimit indexBound state valid wellFormed widthBound matrixBound rankBound freeBound wordsSize
    matrixAt references owned.buffer.values matrixProtected (ownedWords_protects owned) budget
  intro calcStore calcHeap columnNode resultNode calcValid columnOwned resultOwned calcFrame columnFresh resultFresh columnSeparated calcBudget calcLocals calcState columnRead
  dsimp only [Sequence.Fallthrough]
  have differentCurrent : columnNode.root ≠ currentNode.root :=
    columnFresh.pointer_ne currentNode.root words.size (ownedWords_protects owned)
      (by have := columnOwned.buffer.capacity; omega) columnOwned.buffer.rootBound
  have currentResultSeparated := resultFresh.separated owned resultOwned.buffer.rootBound
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((directionBody.drop 107).take 6 ++ (loopArrayCleanupProgram 63 119 117 ++ directionBody.drop 125)) Q store frame env) ?_ (fun _ _ h => h)
  apply directionTemporaryRelease_exact env middle calcStore heap calcHeap params calcLocals columnNode resultNode
    (basis.columns.set! index free.toUInt64)
    (words.set! basis.columns[index].toNat (0 - determinant basis.rows.size input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64)))
    currentNode.root paramsSize calcState.size columnRead calcState.currentOwner differentCurrent columnSeparated remaining pageLimit
    calcValid columnOwned resultOwned calcFrame columnFresh calcBudget
  intro tempValid tempOwned tempFrame tempBudget
  dsimp only [Sequence.Fallthrough]
  let tempStore := calcHeap.releaseStore calcStore columnNode
  let tempHeap := calcHeap.release columnNode
  let tempLocals := (directionResultLocals calcLocals resultNode.root).set 82 (.i64 (calcHeap.frees + 1))
  have tempState := directionTemporary_state calcState resultNode.root (calcHeap.frees + 1)
  have tempSize : tempLocals.length = 112 := tempState.size
  let ready := directionHandoffLocals tempLocals resultNode.root
  have readyState := directionHandoff_state tempState resultNode.root
  have readySize : ready.length = 112 := readyState.size
  refine Sequence.wp_append (P := fun store frame => store = tempStore ∧ frame = { params := params, locals := ready }) ?_ ?_
  · apply directionHandoff_exact env tempStore params tempLocals resultNode.root paramsSize tempState.size
    · simp [tempLocals, directionResultLocals, calcState.size]
    · simp [tempLocals, directionResultLocals, calcState.size]
    · simp [tempLocals, directionResultLocals, calcState.size]
    · exact ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply loopArrayCleanup_exact env initial tempStore originalHeap tempHeap
    { params := params, locals := ready } 63 119 117 currentNode resultNode words
    (words.set! basis.columns[index].toNat (0 - determinant basis.rows.size input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64)))
    original remaining pageLimit tempValid (tempFrame.ownsWords tempValid owned) tempOwned
    (preserved.trans tempFrame) active currentResultSeparated tempBudget rfl
  · simpa only [Locals.get, paramsSize, readySize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using readyState.currentOwner
  · simpa only [Locals.get, paramsSize, readySize, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using readyState.originalOwner
  · simp [Locals.get, paramsSize, ready, directionHandoffLocals, tempSize]
  · intro final finalHeap finalValid finalOwned finalFrame finalBudget
    apply directionAdvance_exact env final params ready resultNode.root index indexSmall paramsSize readyState.size
    · simp [ready, directionHandoffLocals, tempSize]
    · simp [ready, directionHandoffLocals, tempSize]
    · simp [ready, directionHandoffLocals, tempSize]
    · exact readyState.position
    · exact readyState.step
    · exact next final finalHeap resultNode finalValid finalOwned finalFrame (resultFresh.original preserved) finalBudget _
        (directionAdvance_state readyState resultNode.root)

#print axioms directionStep_exact

end Project.Beck.Execution
