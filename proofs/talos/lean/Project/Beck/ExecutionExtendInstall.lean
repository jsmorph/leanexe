import Project.Beck.ExecutionExtendCleanup

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendInstalledLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : List Value :=
  let tag : UInt64 := if found then 1 else 0
  let r := if found then rows else 0
  let c := if found then columns else 0
  let d := if found then value else 0
  let l := extendSelectedLocals locals found rows columns value
  let l := (((l.set 129 (.i64 tag)).set 130 (.i64 r)).set 131 (.i64 r)).set 132 (.i64 c)
  let l := (((l.set 133 (.i64 c)).set 134 (.i64 d)).set 135 (.i64 0)).set 128 (.i64 tag)
  let l := (((l.set 8 (.i64 tag)).set 9 (.i64 r)).set 10 (.i64 r)).set 11 (.i64 c)
  ((l.set 12 (.i64 c)).set 13 (.i64 d)).set 14 (.i64 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendInstall_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (emptyRows : locals[9]? = some (.i64 0)) (emptyColumns : locals[11]? = some (.i64 0))
    (oldRows : locals[137]? = some (.i64 0)) (oldColumns : locals[139]? = some (.i64 0))
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := extendInstalledLocals locals found rows columns value })) :
    wp Project.Beck.«module» ((extendColumnBody.drop 125).take 74) Q initial
      { params := params, locals := extendSelectedLocals locals found rows columns value } env := by
  cases found
  all_goals
    simp only [extendColumnBody, extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, extendSelectedLocals, Bool.false_eq_true, reduceIte]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          emptyRows, emptyColumns, oldRows, oldColumns, UInt32.zero_and, UInt32.and_zero,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals exact next

#print axioms extendInstall_exact

end Project.Beck.Execution
