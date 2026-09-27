import Project.Beck.ExecutionExtendReturn

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem extend_function_shape : func26 = func26.take 35 ++
    ([.block 0 0 [.loop 0 0 extendBody]] ++ func26.drop 36) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extend_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size < 6)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columnPointer.toNat (columnPointer.toNat + 8 * (basis.columns.size + 1)))
    (budget : OutputBudget initial heap ((208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width) + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 26 initial
      (extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer).reverse
      (fun final values => ∃ finalHeap, finalHeap.At final ∧ heap.Frame initial finalHeap final ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        ExtendOutput heap finalHeap final basis rowOwner rowPointer columnOwner columnPointer
          (Project.Beck.Basis.extension width matrix basis) values) := by
  refine TerminatesWith.of_wp_entry_for (f := func26Def) rfl ?_
  change wp Project.Beck.«module» func26 _ initial
    { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      locals := List.replicate 158 (.i64 0) } env
  rw [extend_function_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      locals := extendEntryLocals (List.replicate 158 (.i64 0)) width matrix.size matrixPointer })
  · exact extendEntry_exact env initial (List.replicate 158 (.i64 0)) width matrix matrixOwner matrixPointer basis
      rowOwner rowPointer columnOwner columnPointer (by simp) widthBound matrixAt _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  apply extendOuterLoop_exact env initial heap width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
    _ remaining pageLimit valid wellFormed widthBound matrixBound rankBound
    (extendEntry_state _ (by simp) width matrix.size matrixPointer) matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget
  intro final finalHeap finalValid finalFrame finalBudget nextLocals output
  cases extension : Project.Beck.Basis.extension width matrix basis with
  | none =>
    simp only [extension, ExtendOuterOutput] at output
    apply extendReturn_exact env final nextLocals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer false 0 0 0 output
    intro returned correct
    refine ⟨finalHeap, finalValid, finalFrame, finalBudget, ?_⟩
    simp only [func26Def, correct, Bool.false_eq_true, reduceIte, extension, ExtendOutput, basisValues, List.take]
    rfl
  | some result =>
    simp only [extension, ExtendOuterOutput] at output
    obtain ⟨rowsNode, columnsNode, owned, choice⟩ := output
    apply extendReturn_exact env final nextLocals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      true rowsNode.root columnsNode.root result.determinant choice
    intro returned correct
    refine ⟨finalHeap, finalValid, finalFrame, finalBudget, ?_⟩
    simp only [func26Def, correct, reduceIte, extension, ExtendOutput, List.take]
    exact ⟨rowsNode, columnsNode, owned, rfl⟩

#print axioms extend_exact

end Project.Beck.Execution
