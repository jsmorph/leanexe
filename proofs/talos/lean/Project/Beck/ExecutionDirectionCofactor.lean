import Project.Beck.ExecutionDirectionCofactorState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionCofactorBytes (basis : Basis) (jobs : Nat) : Nat :=
  48 + 8 * (basis.columns.size + 1) + determinantBytes basis.rows.size + (48 + 8 * (jobs + 1))

set_option maxRecDepth 4096 in
theorem direction_cofactor_shape : (directionBody.drop 4).take 86 =
    (directionBody.drop 4).take 22 ++ ((directionBody.drop 26).take 32 ++ (directionBody.drop 58).take 32) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionCofactor_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (matrix words : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp original current : UInt64)
    (free index remaining pageLimit : Nat) (indexBound : index < basis.columns.size)
    (state : DirectionLoopLocals locals matrixPointer sro srp sco scp basis ro rp co cp original current free index)
    (valid : heap.At initial) (wellFormed : Project.Beck.Basis.WellFormed input.jobs matrix basis)
    (widthBound : input.jobs ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size ≤ 6)
    (freeBound : free < input.jobs) (wordsSize : words.size = input.jobs)
    (matrixAt : UInt64Array.At initial matrixPointer matrix) (references : BasisReferences heap initial basis rp cp)
    (wordsAt : UInt64Array.At initial current words)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (wordsProtected : heap.Protects current.toNat (current.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (directionCofactorBytes basis input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap columnsNode resultNode, finalHeap.At final →
      finalHeap.OwnsWords final columnsNode (basis.columns.set! index free.toUInt64) →
      finalHeap.OwnsWords final resultNode
        (words.set! basis.columns[index].toNat (0 - determinant basis.rows.size input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64))) →
      heap.Frame initial finalHeap final → FreshFor heap columnsNode → FreshFor heap resultNode →
      regionsDisjoint columnsNode.region resultNode.region →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, DirectionLoopLocals nextLocals matrixPointer sro srp sco scp basis ro rp co cp original current free index →
      nextLocals[62]? = some (.i64 columnsNode.root) →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
          locals := nextLocals, values := [.i64 resultNode.root] })) :
    wp Project.Beck.«module» ((directionBody.drop 4).take 86) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
  have paramsSize : params.length = 9 := by simp [params, matrixParams, inputValues, pointValues]
  have columnsBound : basis.columns.size ≤ 56 := by rw [← wellFormed.square]; omega
  let resultBytes := 48 + 8 * (words.size + 1)
  rw [direction_cofactor_shape]
  refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
    ((directionBody.drop 26).take 32 ++ (directionBody.drop 58).take 32) Q store frame env) ?_ (fun _ _ h => h)
  apply directionColumn_exact env initial heap params locals state.words paramsSize state.size cp current basis.columns free index
    state.columnPointer state.currentPointer state.freeColumn state.position
    (determinantBytes basis.rows.size + (resultBytes + remaining)) pageLimit valid columnsBound indexBound
    references.columnsAt references.columnsProtected
  · simpa only [directionCofactorBytes, resultBytes, wordsSize, Nat.add_assoc] using budget
  · intro columnStore
    dsimp only
    intro columnValid columnOwned columnFrame columnFresh columnBudget columnLocals columnChange
    dsimp only [Sequence.Fallthrough]
    let columnHeap := heap.allocate (UInt64.ofNat (8 * (basis.columns.size + 1)))
    let columnNode := allocatedNode heap.top (UInt64.ofNat (8 * (basis.columns.size + 1))) heap.nodes
    have columnState := (directionColumn_state state).updated columnChange
    have indexSaved : columnLocals[56]? = some (.i64 index.toUInt64) := by
      rw [columnChange.keeps 56 (Or.inl (by omega))]
      simp [directionColumnLocals, state.size]
    have currentSaved : columnLocals[58]? = some (.i64 current) := by
      rw [columnChange.keeps 58 (Or.inl (by omega))]
      simp [directionColumnLocals, state.size]
    refine Sequence.wp_append (P := fun store frame => wp Project.Beck.«module»
      ((directionBody.drop 58).take 32) Q store frame env) ?_ (fun _ _ h => h)
    apply directionDeterminant_exact env columnStore columnHeap columnLocals input point basis matrix
      inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp columnNode.root
      free index (resultBytes + remaining) pageLimit columnState.toDirectionSearchLocals columnValid wellFormed
      widthBound matrixBound rankBound freeBound
      (columnFrame.words matrixProtected matrixAt) (columnFrame.words references.rowsProtected references.rowsAt)
      columnOwned.buffer.values (columnFrame.protects _ _ matrixProtected)
      (columnFrame.protects _ _ references.rowsProtected) (ownedWords_protects columnOwned) columnBudget
    intro detStore detHeap detValid detFrame detBudget
    dsimp only [Sequence.Fallthrough]
    let detLocals := directionDetLocals columnLocals basis.rows.size input.jobs matrixPointer ro rp columnNode.root
    have detState := directionDet_state columnState input.jobs columnNode.root
    have detPreserved := columnFrame.trans detFrame
    have detIndex : detLocals[56]? = some (.i64 index.toUInt64) := by
      simpa only [detLocals, directionDetLocals, List.getElem?_set, List.length_set,
        columnState.size, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using indexSaved
    have detCurrent : detLocals[58]? = some (.i64 current) := by
      simpa only [detLocals, directionDetLocals, List.getElem?_set, List.length_set,
        columnState.size, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using currentSaved
    have targetBound : basis.columns[index].toNat < words.size := by
      rw [wordsSize]
      exact wellFormed.columns.bound _ (Array.getElem_mem indexBound)
    have columnAfterDet := detFrame.ownsWords detValid columnOwned
    apply directionCoefficient_exact env detStore detHeap params detLocals detState.words paramsSize detState.size current cp
      (determinant basis.rows.size input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64))
      words basis.columns index indexBound detState.columnPointer detCurrent detIndex
      (detPreserved.words references.columnsProtected references.columnsAt) remaining pageLimit detValid
      (by rw [wordsSize]; omega) targetBound (detPreserved.words wordsProtected wordsAt)
      (detPreserved.protects _ _ wordsProtected) detBudget
    intro final
    dsimp only
    intro finalValid resultOwned resultFrame resultFresh finalBudget nextLocals resultChange
    have finalState := (directionCoefficient_state detState _ _).updated resultChange
    apply next final _ columnNode _ finalValid (resultFrame.ownsWords finalValid columnAfterDet) resultOwned
      (detPreserved.trans resultFrame) columnFresh (resultFresh.original detPreserved)
      (resultFresh.separated columnAfterDet resultOwned.buffer.rootBound) finalBudget nextLocals finalState
    rw [resultChange.keeps 62 (Or.inl (by omega))]
    simp only [directionCoefficientLocals, directionCoefficientPrepared, detLocals, directionDetLocals,
      List.getElem?_set, List.length_set, columnState.size, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]

#print axioms directionCofactor_exact

end Project.Beck.Execution
