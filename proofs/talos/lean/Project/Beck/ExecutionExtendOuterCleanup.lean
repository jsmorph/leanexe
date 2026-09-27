import Project.Beck.ExecutionExtendOuterSelect

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendOuterHandledLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : List Value :=
  (extendOuterSelectedLocals locals found rows columns value).set 101 (.i64 (if found then 1 else 0))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem extendOuterCleanup_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (emptyRows : locals[1]? = some (.i64 0)) (emptyColumns : locals[3]? = some (.i64 0))
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := extendOuterHandledLocals locals found rows columns value })) :
    wp Project.Beck.«module» ((extendBody.drop 109).take 51) Q initial
      { params := params, locals := extendOuterSelectedLocals locals found rows columns value } env := by
  cases found
  all_goals by_cases rowsZero : rows = 0
  all_goals by_cases columnsZero : columns = 0
  all_goals by_cases same : rows = columns
  all_goals
    simp only [extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, extendOuterSelectedLocals, Bool.false_eq_true, reduceIte]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          emptyRows, emptyColumns, rowsZero, columnsZero, same,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals simpa only [extendOuterHandledLocals, extendOuterSelectedLocals, Bool.false_eq_true, rowsZero, columnsZero, same, reduceIte] using next

#print axioms extendOuterCleanup_exact

end Project.Beck.Execution
