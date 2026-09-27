import Project.Beck.ExecutionFindBasisFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem find_basis_step_shape : findBasisBody.drop 7 =
    (findBasisBody.drop 7).take 24 ++ (.call 26 :: findBasisBody.drop 32) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem findBasisStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (fuel width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (locals : List Value)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rowsBound : matrix.size / width < 6)
    (state : FindBasisLocals locals false basis rowOwner rowPointer columnOwner columnPointer)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (refs : BasisReferences heap initial basis rowPointer columnPointer)
    (budget : OutputBudget initial heap (findBasisRoundBytes width matrix + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (stopped : Project.Beck.Basis.extension width matrix basis = none →
      ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
        ∀ nextLocals, FindBasisLocals nextLocals true basis rowOwner rowPointer columnOwner columnPointer →
          Q (.Break 0 final
            { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
              locals := nextLocals }))
    (growing : ∀ nextBasis, Project.Beck.Basis.extension width matrix basis = some nextBasis →
      ∀ final finalHeap rowsNode columnsNode, finalHeap.At final → heap.Frame initial finalHeap final →
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
        CandidateBasis heap finalHeap final nextBasis rowsNode columnsNode →
        ∀ nextLocals, FindBasisLocals nextLocals false nextBasis rowsNode.root rowsNode.root columnsNode.root columnsNode.root →
          Q (.Break 0 final
            { params := findBasisParams fuel width matrixOwner matrixPointer nextBasis rowsNode.root rowsNode.root columnsNode.root columnsNode.root
              locals := nextLocals })) :
    wp Project.Beck.«module» (findBasisBody.drop 7) Q initial
      { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := locals } env := by
  let params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  let prepared := findBasisPreparedLocals locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
  have preparedState := findBasisPrepared_state state width matrixOwner matrixPointer
  have rankBound := (Project.Beck.Basis.indices_size wellFormed.rows).trans_lt rowsBound
  have call := extend_exact env initial heap width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
    remaining pageLimit valid wellFormed widthBound matrixBound rankBound matrixAt refs.rowsAt refs.columnsAt
    matrixProtected refs.rowsProtected refs.columnsProtected (budget.mono (Nat.add_le_add_right (extend_bytes_bound rankBound) remaining))
  rw [find_basis_step_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := params, locals := prepared,
      values := (extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer).reverse })
  · exact findBasisPrepare_exact env initial locals (fuel + 1) width matrixOwner matrixPointer basis
      rowOwner rowPointer columnOwner columnPointer state.size _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  refine wp_call_tw call ?_
  rintro final values ⟨finalHeap, finalValid, finalFrame, finalBudget, output⟩
  change wp Project.Beck.«module» (findBasisBody.drop 32) Q final { params := params, locals := prepared, values := values } env
  cases extension : Project.Beck.Basis.extension width matrix basis with
  | none =>
    simp only [extension, ExtendOutput] at output
    subst values
    apply findBasisAfter_exact env final prepared fuel width matrixOwner matrixPointer basis basis
      rowOwner rowPointer columnOwner columnPointer rowOwner rowPointer columnOwner columnPointer
      preparedState.size preparedState.owner9 preparedState.owner10 preparedState.owner11
      (finalFrame.words refs.rowsProtected refs.rowsAt) (finalFrame.words refs.rowsProtected refs.rowsAt)
    · intro _
      exact stopped extension final finalHeap finalValid finalFrame finalBudget _
        (findBasisStopped_state (findBasisRead_state preparedState basis rowOwner rowPointer columnOwner columnPointer))
    · intro impossible
      exact False.elim (impossible rfl)
  | some nextBasis =>
    simp only [extension, ExtendOutput] at output
    obtain ⟨rowsNode, columnsNode, owned, rfl⟩ := output
    apply findBasisAfter_exact env final prepared fuel width matrixOwner matrixPointer basis nextBasis
      rowOwner rowPointer columnOwner columnPointer rowsNode.root rowsNode.root columnsNode.root columnsNode.root
      preparedState.size preparedState.owner9 preparedState.owner10 preparedState.owner11
      (finalFrame.words refs.rowsProtected refs.rowsAt) owned.references.rowsAt
    · intro same
      obtain ⟨row, _, column, _, candidate⟩ := Project.Beck.Basis.extension_some width matrix basis nextBasis extension
      have grows := (Project.Beck.Basis.candidate_grows width matrix basis nextBasis row column candidate).1
      rw [grows, Array.size_push] at same
      omega
    · intro _
      exact growing nextBasis extension final finalHeap rowsNode columnsNode finalValid finalFrame finalBudget owned _
        (findBasisContinued_state preparedState width matrixOwner matrixPointer nextBasis rowsNode.root rowsNode.root columnsNode.root columnsNode.root)

#print axioms findBasisStep_exact

end Project.Beck.Execution
