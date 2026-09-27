import Project.Beck.ExecutionExtendOuterPrepare

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendOuterSelectedLocals (locals : List Value) (found : Bool) (rows columns value : UInt64) : List Value :=
  let tag : UInt64 := if found then 1 else 0
  let absent : UInt64 := if found then 0 else 1
  let r := if found then rows else 0
  let c := if found then columns else 0
  let d := if found then value else 0
  let l := locals
  let l := ((((l.set 56 (.i64 tag)).set 57 (.i64 r)).set 58 (.i64 r)).set 59 (.i64 c))
  let l := ((((l.set 60 (.i64 c)).set 61 (.i64 d)).set 62 (.i64 0)).set 63 (.i64 tag))
  let l := ((((l.set 64 (.i64 r)).set 65 (.i64 r)).set 66 (.i64 c)).set 67 (.i64 c))
  let l := ((((l.set 68 (.i64 d)).set 70 (.i64 absent)).set 71 (.i64 tag)).set 72 (.i64 r))
  let l := ((((l.set 73 (.i64 r)).set 74 (.i64 c)).set 75 (.i64 c)).set 76 (.i64 d))
  let l := ((((l.set 77 (.i64 0)).set 78 (.i64 0)).set 79 (.i64 0)).set 80 (.i64 0))
  let l := ((((l.set 81 (.i64 0)).set 82 (.i64 0)).set 83 (.i64 0)).set 84 (.i64 0))
  let l := ((((l.set 85 (.i64 tag)).set 86 (.i64 r)).set 87 (.i64 r)).set 88 (.i64 c))
  ((((l.set 89 (.i64 c)).set 90 (.i64 d)).set 91 (.i64 0)).set 92 (.i64 tag))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendOuterSelect_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (paramsSize : params.length = 8) (localsSize : locals.length = 158)
    (found : Bool) (rows columns value : UInt64)
    (choice : ExtendChoiceLocals locals found rows columns value) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := extendOuterSelectedLocals locals found rows columns value })) :
    wp Project.Beck.«module» ((extendBody.drop 31).take 78) Q initial
      { params := params, locals := locals } env := by
  cases found
  all_goals
    simp only [extendBody, func26, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
    repeat' first
      | (wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          choice.tag, choice.rowsOwner, choice.rowsPointer, choice.columnsOwner, choice.columnsPointer,
          choice.determinant, choice.extraOwner, Bool.false_eq_true,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals exact next

#print axioms extendOuterSelect_exact

end Project.Beck.Execution

