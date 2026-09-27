import Project.Beck.ExecutionDirectionSeed

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure DirectionBasisLocals (locals : List Value) (jobs : Nat) (matrix ro rp co cp : UInt64) : Prop where
  size : locals.length = 112
  fuel : locals[13]? = some (.i64 jobs.toUInt64)
  width : locals[14]? = some (.i64 jobs.toUInt64)
  matrixOwner : locals[15]? = some (.i64 matrix)
  matrixPointer : locals[16]? = some (.i64 matrix)
  rowOwner : locals[19]? = some (.i64 ro)
  rowPointer : locals[20]? = some (.i64 rp)
  columnOwner : locals[21]? = some (.i64 co)
  columnPointer : locals[22]? = some (.i64 cp)

set_option maxRecDepth 4096 in
theorem directionBasisPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (jobs : Nat) (matrix ro rp co cp : UInt64) (paramsSize : params.length = 9)
    (state : DirectionBasisLocals locals jobs matrix ro rp co cp) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := params, locals := locals.set 23 (.i64 1),
        values := (findBasisParams jobs jobs matrix matrix ⟨#[], #[], 1⟩ ro rp co cp).reverse })) :
    wp Project.Beck.«module» ((func30.drop 214).take 11) Q initial { params := params, locals := locals } env := by
  simp only [func30, List.drop, List.take]
  wp_run [paramsSize, state.size, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
    state.fuel, state.width, state.matrixOwner, state.matrixPointer, state.rowOwner, state.rowPointer, state.columnOwner, state.columnPointer]
  exact next

set_option maxRecDepth 4096 in
theorem direction_basis_shape : (func30.drop 214).take 12 = (func30.drop 214).take 11 ++ [.call 27] := rfl

set_option maxRecDepth 4096 in
theorem directionBasis_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (jobs : Nat) (matrix : Array UInt64) (matrixPointer : UInt64)
    (ro rp co cp : UInt64) (paramsSize : params.length = 9)
    (state : DirectionBasisLocals locals jobs matrixPointer ro rp co cp)
    (remaining pageLimit : Nat) (valid : heap.At initial) (jobsBound : jobs ≤ 6)
    (matrixBound : matrix.size ≤ 56) (rowsBound : matrix.size / jobs < 6)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (refs : BasisReferences heap initial ⟨#[], #[], 1⟩ rp cp)
    (budget : OutputBudget initial heap (findBasisRoundBytes jobs matrix * jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap rOwner rPointer cOwner cPointer, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      BasisReferences finalHeap final (findBasis jobs jobs matrix ⟨#[], #[], 1⟩) rPointer cPointer →
      BasisOutput heap finalHeap final ⟨#[], #[], 1⟩ (basisValues ⟨#[], #[], 1⟩ ro rp co cp)
        (findBasis jobs jobs matrix ⟨#[], #[], 1⟩) (basisValues (findBasis jobs jobs matrix ⟨#[], #[], 1⟩) rOwner rPointer cOwner cPointer) →
      Q (.Fallthrough final
        { params := params, locals := locals.set 23 (.i64 1),
          values := basisValues (findBasis jobs jobs matrix ⟨#[], #[], 1⟩) rOwner rPointer cOwner cPointer })) :
    wp Project.Beck.«module» ((func30.drop 214).take 12) Q initial { params := params, locals := locals } env := by
  rw [direction_basis_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := params, locals := locals.set 23 (.i64 1), values := (findBasisParams jobs jobs matrixPointer matrixPointer ⟨#[], #[], 1⟩ ro rp co cp).reverse })
  · exact directionBasisPrepare_exact env initial params locals jobs matrixPointer ro rp co cp paramsSize state _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  refine wp_call_tw (findBasis_exact env initial heap jobs jobs matrix matrixPointer matrixPointer ⟨#[], #[], 1⟩ ro rp co cp
    remaining pageLimit valid (Project.Beck.Basis.empty_wellFormed jobs matrix) jobsBound jobsBound matrixBound rowsBound matrixAt matrixProtected refs budget) ?_
  rintro final values ⟨finalHeap, rOwner, rPointer, cOwner, cPointer, finalValid, finalFrame, finalBudget, rfl, finalRefs, output⟩
  rw [wp_nil]
  exact next final finalHeap rOwner rPointer cOwner cPointer finalValid finalFrame finalBudget finalRefs output

#print axioms directionBasis_exact

end Project.Beck.Execution
