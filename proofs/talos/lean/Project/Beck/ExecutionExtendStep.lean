import Project.Beck.ExecutionExtendStable

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem extend_column_step_shape : extendColumnBody.drop 4 =
    (extendColumnBody.drop 4).take 32 ++ (.call 25 :: extendColumnBody.drop 37) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendColumnStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat) (locals : List Value)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size < 6)
    (rowBound : row < matrix.size / width) (columnBound : column < width)
    (state : ExtendSearchLocals locals row (matrix.size / width) column width)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap (208 + determinantBytes (basis.rows.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (nextNone : borderCandidate width matrix basis row column = none →
      ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
        ∀ nextLocals, ExtendSearchLocals nextLocals row (matrix.size / width) (column + 1) width →
          Q (.Break 0 final { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := nextLocals }))
    (found : ∀ result, borderCandidate width matrix basis row column = some result →
      ∀ final finalHeap rowsNode columnsNode, finalHeap.At final → heap.Frame initial finalHeap final →
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
        CandidateBasis heap finalHeap final result rowsNode columnsNode →
        ∀ nextLocals, ExtendScanLocals nextLocals row (matrix.size / width) width →
          ExtendChoiceLocals nextLocals true rowsNode.root columnsNode.root result.determinant →
          Q (.Break 1 final { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := nextLocals })) :
    wp Project.Beck.«module» (extendColumnBody.drop 4) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  let params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  let prepared := extendPreparedLocals locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column
  have paramsSize : params.length = 8 := by simp [params, extendParams, basisValues]
  have preparedState : ExtendSearchLocals prepared row (matrix.size / width) column width :=
    extendPrepared_search state matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  have input := extend_candidate_input wellFormed widthBound matrixBound rankBound row column rowBound columnBound
  have call := borderCandidate_exact env initial heap width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
    row column remaining pageLimit valid input matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget
  rw [extend_column_step_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := params, locals := prepared,
      values := (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column).reverse })
  · exact extendPrepare_exact env initial locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      row column state.size state.currentRow state.columnIndex _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  refine wp_call_tw call ?_
  rintro final values ⟨finalHeap, finalValid, finalFrame, finalBudget, output⟩
  change wp Project.Beck.«module» (extendColumnBody.drop 37) Q final { params := params, locals := prepared, values := values } env
  cases candidate : borderCandidate width matrix basis row column with
  | none =>
    simp only [candidate, CandidateOutput] at output
    subst values
    apply extendAfterCandidate_exact env final params prepared paramsSize preparedState.size
      (preparedState.innerEmpty 9 (by decide) (by decide)) (preparedState.innerEmpty 11 (by decide) (by decide))
      preparedState.oldRows preparedState.oldColumns column (by omega) preparedState.columnIndex preparedState.columnStep false 0 0 0
    exact nextNone candidate final finalHeap finalValid finalFrame finalBudget _ (extendContinue_search preparedState)
  | some result =>
    simp only [candidate, CandidateOutput] at output
    obtain ⟨rowsNode, columnsNode, owned, rfl⟩ := output
    apply extendAfterCandidate_exact env final params prepared paramsSize preparedState.size
      (preparedState.innerEmpty 9 (by decide) (by decide)) (preparedState.innerEmpty 11 (by decide) (by decide))
      preparedState.oldRows preparedState.oldColumns column (by omega) preparedState.columnIndex preparedState.columnStep
      true rowsNode.root columnsNode.root result.determinant
    exact found result candidate final finalHeap rowsNode columnsNode finalValid finalFrame finalBudget owned _
      (extendInstalled_scan preparedState.toExtendScanLocals true rowsNode.root columnsNode.root result.determinant)
      (extendInstalled_choice prepared preparedState.size true rowsNode.root columnsNode.root result.determinant)

#print axioms extendColumnStep_exact

end Project.Beck.Execution
