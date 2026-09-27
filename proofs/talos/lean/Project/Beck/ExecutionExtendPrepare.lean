import Project.Beck.ExecutionExtendState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendPreparedLocals (locals : List Value) (width : Nat) (matrixOwner matrixPointer : UInt64)
    (basis : Basis) (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat) : List Value :=
  let l := ((locals.set 15 (.i64 column.toUInt64)).set 16 (.i64 width.toUInt64)).set 17 (.i64 matrixOwner)
  let l := ((l.set 18 (.i64 matrixPointer)).set 19 (.i64 rowOwner)).set 20 (.i64 rowPointer)
  let l := ((l.set 21 (.i64 columnOwner)).set 22 (.i64 columnPointer)).set 23 (.i64 basis.determinant)
  (l.set 24 (.i64 row.toUInt64)).set 25 (.i64 column.toUInt64)

set_option maxRecDepth 2048 in
theorem extendPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (row column : Nat)
    (localsSize : locals.length = 158)
    (rowRead : locals[7]? = some (.i64 row.toUInt64)) (columnRead : locals[125]? = some (.i64 column.toUInt64))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := extendPreparedLocals locals width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column
        values := (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column).reverse })) :
    wp Project.Beck.«module» ((extendColumnBody.drop 4).take 32) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := locals } env := by
  simp only [extendColumnBody, extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    localsSize, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, rowRead, columnRead, reduceIte]
  exact next

#print axioms extendPrepare_exact

end Project.Beck.Execution
