import Project.Beck.ExecutionFindBasisReturn

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem find_basis_function_shape : func27 = func27.take 8 ++
    ([.block 0 0 [.loop 0 0 findBasisBody]] ++ func27.drop 9) := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem findBasis_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (fuel width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (fuelBound : fuel ≤ 6) (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rowsBound : matrix.size / width < 6)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (refs : BasisReferences heap initial basis rowPointer columnPointer)
    (budget : OutputBudget initial heap (findBasisRoundBytes width matrix * fuel + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 27 initial
      (findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer).reverse
      (fun final values => ∃ finalHeap ro rp co cp, finalHeap.At final ∧ heap.Frame initial finalHeap final ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧
        values = basisValues (findBasis fuel width matrix basis) ro rp co cp ∧
        BasisReferences finalHeap final (findBasis fuel width matrix basis) rp cp ∧
        BasisOutput heap finalHeap final basis (basisValues basis rowOwner rowPointer columnOwner columnPointer)
          (findBasis fuel width matrix basis) values) := by
  refine TerminatesWith.of_wp_entry_for (f := func27Def) rfl ?_
  change wp Project.Beck.«module» func27 _ initial
    { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      locals := List.replicate 47 (.i64 0) } env
  rw [find_basis_function_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      locals := List.replicate 47 (.i64 0) })
  · exact findBasisEntry_exact env initial _ (by simp [findBasisParams, extendParams, basisValues]) _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  apply findBasisLoop_exact env initial heap fuel width matrix matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
    _ remaining pageLimit valid wellFormed fuelBound widthBound matrixBound rowsBound
    (findBasisEntry_state basis rowOwner rowPointer columnOwner columnPointer) matrixAt matrixProtected refs budget
  intro final finalHeap finalValid finalFrame finalBudget finalFuel ro rp co cp stopped nextLocals finalRefs output state
  apply findBasisReturn_exact env final nextLocals finalFuel width matrixOwner matrixPointer (findBasis fuel width matrix basis)
    ro rp co cp stopped state
  intro returned correct
  refine ⟨finalHeap, ro, rp, co, cp, finalValid, finalFrame, finalBudget, ?_, finalRefs, ?_⟩
  · simp only [func27Def, correct, basisValues]
    rfl
  · simp only [func27Def, correct]
    exact output

#print axioms findBasis_exact

end Project.Beck.Execution
