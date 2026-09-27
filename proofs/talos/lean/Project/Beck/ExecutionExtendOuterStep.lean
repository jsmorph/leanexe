import Project.Beck.ExecutionExtendOuterAfter

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem extend_outer_step_shape : extendBody.drop 4 =
    (extendBody.drop 4).take 26 ++ ([.block 0 0 [.loop 0 0 extendColumnBody]] ++ extendBody.drop 31) := rfl

set_option maxRecDepth 4096 in
theorem extendOuterStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row : Nat) (locals : List Value)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size < 6)
    (rowBound : row < matrix.size / width) (state : ExtendOuterLocals locals row (matrix.size / width))
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap ((208 + determinantBytes (basis.rows.size + 1)) * width + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (nextNone : (List.range width).findSome? (borderCandidate width matrix basis row) = none →
      ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
        ∀ nextLocals, ExtendOuterLocals nextLocals (row + 1) (matrix.size / width) →
          Q (.Break 0 final { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := nextLocals }))
    (found : ∀ result, (List.range width).findSome? (borderCandidate width matrix basis row) = some result →
      ∀ final finalHeap rowsNode columnsNode, finalHeap.At final → heap.Frame initial finalHeap final →
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
        CandidateBasis heap finalHeap final result rowsNode columnsNode →
        ∀ nextLocals, ExtendOuterChoiceLocals nextLocals true rowsNode.root columnsNode.root result.determinant →
          Q (.Break 1 final { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := nextLocals })) :
    wp Project.Beck.«module» (extendBody.drop 4) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  let params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  let prepared := extendOuterPreparedLocals locals row width
  have paramsSize : params.length = 8 := by simp [params, extendParams, basisValues]
  have preparedState := extendOuterPrepared_search state width
  have rowFit : row < 56 := by have := Nat.div_le_self matrix.size width; omega
  rw [extend_outer_step_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame = { params := params, locals := prepared })
  · exact extendOuterPrepare_exact env initial locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      row state.size state.rowIndex _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  apply extendColumnLoop_exact env initial heap width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
    row prepared remaining pageLimit valid wellFormed widthBound matrixBound rankBound rowBound preparedState
    matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget
  intro final finalHeap finalValid finalFrame finalBudget nextLocals scan output
  cases candidate : (List.range width).findSome? (borderCandidate width matrix basis row) with
  | none =>
    simp only [candidate, ExtendColumnOutput] at output
    apply extendOuterAfter_exact env final params nextLocals paramsSize scan.size
      (scan.outerEmpty 1 (by decide)) (scan.outerEmpty 3 (by decide)) row rowFit scan.rowIndex scan.rowStep false 0 0 0 output
    exact nextNone candidate final finalHeap finalValid finalFrame finalBudget _ (extendOuterContinue_state scan)
  | some result =>
    simp only [candidate, ExtendColumnOutput] at output
    obtain ⟨rowsNode, columnsNode, owned, choice⟩ := output
    apply extendOuterAfter_exact env final params nextLocals paramsSize scan.size
      (scan.outerEmpty 1 (by decide)) (scan.outerEmpty 3 (by decide)) row rowFit scan.rowIndex scan.rowStep
      true rowsNode.root columnsNode.root result.determinant choice
    exact found result candidate final finalHeap rowsNode columnsNode finalValid finalFrame finalBudget owned _
      (extendOuterInstalled_choice nextLocals scan.size true rowsNode.root columnsNode.root result.determinant)

#print axioms extendOuterStep_exact

end Project.Beck.Execution
