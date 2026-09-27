import Project.Beck.ExecutionFindBasisContinue

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def findBasisStop : Wasm.Program := match (findBasisBody[65]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def findBasisStoppedLocals (locals : List Value) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) : List Value :=
  let l := (((locals.set 3 (.i64 rowOwner)).set 4 (.i64 rowPointer)).set 5 (.i64 columnOwner)).set 6 (.i64 columnPointer)
  (l.set 7 (.i64 basis.determinant)).set 8 (.i64 1)

theorem findBasisStop_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (size : locals.length = 47)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisStoppedLocals locals basis rowOwner rowPointer columnOwner columnPointer })) :
    wp Project.Beck.«module» findBasisStop Q initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  simp only [findBasisStop, findBasisBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ]
  wp_run [findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem find_basis_after_read_shape : findBasisBody.drop 65 = [.iff 0 0 findBasisStop findBasisContinue, .br 0] := rfl

set_option maxRecDepth 4096 in
theorem findBasisAfterRead_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis nextBasis : Basis)
    (rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer : UInt64)
    (size : locals.length = 47)
    (owner9 : locals[0]? = some (.i64 0)) (owner10 : locals[1]? = some (.i64 0)) (owner11 : locals[2]? = some (.i64 0))
    (Q : Assertion Unit)
    (stopped : nextBasis.rows.size = basis.rows.size → Q (.Break 0 initial
      { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisStoppedLocals (findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer)
          basis rowOwner rowPointer columnOwner columnPointer }))
    (growing : nextBasis.rows.size ≠ basis.rows.size → Q (.Break 0 initial
      { params := findBasisParams fuel width matrixOwner matrixPointer nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer
        locals := findBasisContinuedLocals locals width matrixOwner matrixPointer nextBasis
          nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer })) :
    wp Project.Beck.«module» (findBasisBody.drop 65) Q initial
      { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer
        values := [.i32 (if nextBasis.rows.size = basis.rows.size then 1 else 0)] } env := by
  rw [find_basis_after_read_shape]
  by_cases same : nextBasis.rows.size = basis.rows.size
  all_goals
    simp only [same, reduceIte]
    refine wp_iff_cons rfl ?_
    simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte]
  · apply findBasisStop_exact env initial _ (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
      (by simp [findBasisReadLocals, size])
    simpa only [List.take_zero, List.drop_zero, List.nil_append, wp_br_cons] using stopped same
  · apply findBasisContinue_exact env initial locals fuel width matrixOwner matrixPointer basis nextBasis
      rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer size owner9 owner10 owner11
    simpa only [List.take_zero, List.drop_zero, List.nil_append, wp_br_cons] using growing same

#print axioms findBasisAfterRead_exact

end Project.Beck.Execution
