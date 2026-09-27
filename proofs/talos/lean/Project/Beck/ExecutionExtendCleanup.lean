import Project.Beck.ExecutionExtendSelect

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem extendCleanup_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (emptyRows : locals[9]? = some (.i64 0)) (emptyColumns : locals[11]? = some (.i64 0))
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := extendSelectedLocals locals found rows columns value })) :
    wp Project.Beck.«module» ((extendColumnBody.drop 95).take 30) Q initial
      { params := params, locals := extendSelectedLocals locals found rows columns value } env := by
  cases found
  all_goals by_cases rowsZero : rows = 0
  all_goals by_cases columnsZero : columns = 0
  all_goals by_cases same : rows = columns
  all_goals
    simp only [extendColumnBody, extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, extendSelectedLocals, Bool.false_eq_true, reduceIte]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          emptyRows, emptyColumns, rowsZero, columnsZero, same,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals simpa only [extendSelectedLocals, Bool.false_eq_true, rowsZero, columnsZero, same, reduceIte] using next

#print axioms extendCleanup_exact

end Project.Beck.Execution
