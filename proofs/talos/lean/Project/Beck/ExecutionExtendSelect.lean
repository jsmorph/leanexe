import Project.Beck.ExecutionExtendState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendSelectedLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : List Value :=
  let tag : UInt64 := if found then 1 else 0
  let absent : UInt64 := if found then 0 else 1
  let r := if found then rows else 0
  let c := if found then columns else 0
  let d := if found then value else 0
  let l := ((((locals.set 31 (.i64 d)).set 30 (.i64 c)).set 29 (.i64 c)).set 28 (.i64 r)).set 27 (.i64 r)
  let l := (((l.set 26 (.i64 tag)).set 32 (.i64 absent)).set 33 (.i64 tag)).set 34 (.i64 r)
  let l := (((l.set 35 (.i64 r)).set 36 (.i64 c)).set 37 (.i64 c)).set 38 (.i64 d)
  let l := (((l.set 39 (.i64 0)).set 40 (.i64 0)).set 41 (.i64 0)).set 42 (.i64 0)
  let l := (((l.set 43 (.i64 0)).set 44 (.i64 0)).set 45 (.i64 0)).set 46 (.i64 0)
  let l := (((l.set 47 (.i64 tag)).set 48 (.i64 r)).set 49 (.i64 r)).set 50 (.i64 c)
  (((l.set 51 (.i64 c)).set 52 (.i64 d)).set 53 (.i64 0)).set 54 (.i64 tag)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendSelect_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (found : Bool) (rows columns value : UInt64) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := extendSelectedLocals locals found rows columns value })) :
    wp Project.Beck.«module» ((extendColumnBody.drop 37).take 58) Q initial
      { params := params, locals := locals, values :=
        if found then [.i64 value, .i64 columns, .i64 columns, .i64 rows, .i64 rows, .i64 1]
        else List.replicate 6 (.i64 0) } env := by
  cases found
  all_goals
    simp only [extendColumnBody, extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, Bool.false_eq_true, reduceIte, List.replicate]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
           ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals exact next

#print axioms extendSelect_exact

end Project.Beck.Execution
