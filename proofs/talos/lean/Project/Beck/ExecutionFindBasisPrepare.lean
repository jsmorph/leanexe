import Project.Beck.ExecutionFindBasisState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def findBasisPreparedLocals (locals : List Value) (width : Nat) (matrixOwner matrixPointer : UInt64)
    (basis : Basis) (rowOwner rowPointer columnOwner columnPointer : UInt64) : List Value :=
  let l := (((locals.set 9 (.i64 width.toUInt64)).set 10 (.i64 matrixOwner)).set 11 (.i64 matrixPointer)).set 12 (.i64 rowOwner)
  (((l.set 13 (.i64 rowPointer)).set 14 (.i64 columnOwner)).set 15 (.i64 columnPointer)).set 16 (.i64 basis.determinant)

set_option maxRecDepth 2048 in
theorem findBasisPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (size : locals.length = 47)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisPreparedLocals locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        values := (extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer).reverse })) :
    wp Project.Beck.«module» ((findBasisBody.drop 7).take 24) Q initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  simp only [findBasisBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

#print axioms findBasisPrepare_exact

end Project.Beck.Execution
