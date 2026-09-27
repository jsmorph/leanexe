import Project.Beck.ExecutionBorderValidate
import Project.Beck.ExecutionBorderResult
import Project.ProofKit.Sequence

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem borderCandidate_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (width : Nat)
    (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat) (remaining pageLimit : Nat)
    (valid : heap.At initial)
    (input : DeterminantInput (basis.rows.size + 1) width matrix (basis.rows.push row.toUInt64) (basis.columns.push column.toUInt64))
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap (208 + determinantBytes (basis.rows.size + 1) + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 25 initial
      (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column).reverse
      (fun final values => ∃ finalHeap, finalHeap.At final ∧ heap.Frame initial finalHeap final ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        CandidateOutput heap finalHeap final (borderCandidate width matrix basis row column) values) := by
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_
  change wp Project.Beck.«module» func25 _ initial
    (borderFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column)
      (fun _ => .i64 0) (fun _ => 0)) env
  rw [← List.take_append_drop 22 func25]
  apply Sequence.wp_append (P := fun final frame => ∃ finalHeap, finalHeap.At final ∧ heap.Frame initial finalHeap final ∧
    OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
    CandidateFrame heap finalHeap final (borderCandidate width matrix basis row column) frame)
  · apply borderValidate_exact env initial width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      row column _ _ rowsAt columnsAt
    · intro duplicate frame result
      refine ⟨heap, valid, Heap.Frame.refl heap initial, budget.mono (by omega), ?_⟩
      simpa [CandidateFrame, borderCandidate, duplicate] using result
    · intro rowsMissing columnsMissing
      apply borderEligible_exact env initial heap width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        row column _ _ remaining pageLimit valid input matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget
      intro final finalHeap rowsNode columnsNode finalValid rowsOwned columnsOwned finalFrame rowsFresh columnsFresh separated finalBudget frame result
      change ∃ finalHeap, finalHeap.At final ∧ heap.Frame initial finalHeap final ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        CandidateFrame heap finalHeap final (borderCandidate width matrix basis row column) { frame with values := [] }
      rw [show ({ frame with values := [] } : Locals) = frame from Frame.ext _ _ rfl rfl result.values.symm]
      refine ⟨finalHeap, finalValid, finalFrame, finalBudget, ?_⟩
      by_cases zero : determinant (basis.rows.size + 1) width matrix (basis.rows.push row.toUInt64) (basis.columns.push column.toUInt64) = 0
      · have result' : BorderResult frame rowsNode.root columnsNode.root 0 := by simpa only [zero] using result
        simpa [CandidateFrame, borderCandidate, rowsMissing, columnsMissing, zero] using result'.zero
      · simp only [borderCandidate, rowsMissing, columnsMissing, Bool.or_self, Bool.false_eq_true, reduceIte,
          Array.size_push, beq_iff_eq, zero, ite_false, CandidateFrame]
        exact ⟨rowsNode, columnsNode, ⟨rowsOwned, columnsOwned, rowsFresh, columnsFresh, separated⟩, zero, result⟩
  · rintro final frame ⟨finalHeap, finalValid, finalFrame, finalBudget, result⟩
    apply borderReturn_exact env final heap finalHeap frame (borderCandidate width matrix basis row column) result
    intro returned output
    refine ⟨finalHeap, finalValid, finalFrame, finalBudget, ?_⟩
    have bound : returned.values.length = 6 := by
      cases candidate : borderCandidate width matrix basis row column with
      | none =>
        simp only [candidate, CandidateOutput] at output
        simp [output]
      | some basis =>
        simp only [candidate, CandidateOutput] at output
        obtain ⟨rows, columns, _, values⟩ := output
        simp [values, basisValues]
    simpa [func25Def, Wasm.Function.numParams, borderParams, basisValues, List.take_of_length_le (by omega : returned.values.length ≤ 6)] using output

#print axioms borderCandidate_exact

end Project.Beck.Execution
