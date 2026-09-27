import Project.Beck.ExecutionFindBasisStop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
theorem find_basis_after_shape : findBasisBody.drop 32 = (findBasisBody.drop 32).take 33 ++ findBasisBody.drop 65 := rfl

set_option maxRecDepth 4096 in
theorem findBasisAfter_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis nextBasis : Basis)
    (rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer : UInt64)
    (size : locals.length = 47)
    (owner9 : locals[0]? = some (.i64 0)) (owner10 : locals[1]? = some (.i64 0)) (owner11 : locals[2]? = some (.i64 0))
    (oldRows : UInt64Array.At initial rowPointer basis.rows) (newRows : UInt64Array.At initial nextRowPointer nextBasis.rows)
    (Q : Assertion Unit)
    (stopped : nextBasis.rows.size = basis.rows.size → Q (.Break 0 initial
      { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisStoppedLocals (findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer)
          basis rowOwner rowPointer columnOwner columnPointer }))
    (growing : nextBasis.rows.size ≠ basis.rows.size → Q (.Break 0 initial
      { params := findBasisParams fuel width matrixOwner matrixPointer nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer
        locals := findBasisContinuedLocals locals width matrixOwner matrixPointer nextBasis
          nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer })) :
    wp Project.Beck.«module» (findBasisBody.drop 32) Q initial
      { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := locals
        values := basisValues nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer } env := by
  rw [find_basis_after_shape]
  apply Sequence.wp_append (P := fun st frame => st = initial ∧ frame =
    { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      locals := findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer
      values := [.i32 (if nextBasis.rows.size = basis.rows.size then 1 else 0)] })
  · exact findBasisRead_exact env initial locals (fuel + 1) width matrixOwner matrixPointer basis nextBasis
      rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer
      size oldRows newRows _ ⟨rfl, rfl⟩
  rintro st frame ⟨same, frameSame⟩
  subst st frame
  exact findBasisAfterRead_exact env initial locals fuel width matrixOwner matrixPointer basis nextBasis
    rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer
    size owner9 owner10 owner11 Q stopped growing

#print axioms findBasisAfter_exact

end Project.Beck.Execution
