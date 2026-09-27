import Project.Beck.ExecutionFindBasisRead

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def findBasisContinuedLocals (locals : List Value) (width : Nat) (matrixOwner matrixPointer : UInt64)
    (nextBasis : Basis) (nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer oldRowPointer : UInt64) : List Value :=
  let l := findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer oldRowPointer
  let l := ((((l.set 27 (.i64 width.toUInt64)).set 28 (.i64 matrixOwner)).set 29 (.i64 matrixPointer)).set 30 (.i64 nextRowOwner))
  let l := ((((l.set 31 (.i64 nextRowPointer)).set 32 (.i64 nextColumnOwner)).set 33 (.i64 nextColumnPointer)).set 34 (.i64 nextBasis.determinant))
  let l := ((((l.set 35 (.i64 width.toUInt64)).set 36 (.i64 matrixOwner)).set 37 (.i64 matrixPointer)).set 38 (.i64 nextRowOwner))
  let l := ((((l.set 39 (.i64 nextRowPointer)).set 40 (.i64 nextColumnOwner)).set 41 (.i64 nextColumnPointer)).set 42 (.i64 nextBasis.determinant))
  let l := ((((l.set 43 (.i64 0)).set 44 (.i64 0)).set 45 (.i64 0)).set 0 (.i64 0))
  ((l.set 1 (.i64 0)).set 2 (.i64 0))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem findBasisContinue_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis nextBasis : Basis)
    (rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer : UInt64)
    (size : locals.length = 47)
    (owner9 : locals[0]? = some (.i64 0)) (owner10 : locals[1]? = some (.i64 0)) (owner11 : locals[2]? = some (.i64 0))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := findBasisParams fuel width matrixOwner matrixPointer nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer
        locals := findBasisContinuedLocals locals width matrixOwner matrixPointer nextBasis
          nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer })) :
    wp Project.Beck.«module» findBasisContinue Q initial
      { params := findBasisParams (fuel + 1) width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer } env := by
  have subtract : (fuel + 1).toUInt64 - 1 = fuel.toUInt64 := by
    change UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel
    rw [UInt64.ofNat_add]
    exact UInt64.add_sub_cancel _ _
  by_cases matrixZero : matrixOwner = 0
  all_goals by_cases rowsZero : nextRowOwner = 0
  all_goals by_cases columnsZero : nextColumnOwner = 0
  all_goals
    simp only [findBasisContinue, findBasisBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ, findBasisReadLocals]
    repeat' first
      | (wp_run [findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          owner9, owner10, owner11, matrixZero, rowsZero, columnsZero,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals simpa only [findBasisContinuedLocals, findBasisReadLocals, findBasisParams, extendParams, basisValues,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append, matrixZero, rowsZero, columnsZero, subtract, reduceIte] using next

#print axioms findBasisContinue_exact

end Project.Beck.Execution

