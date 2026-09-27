import Project.Beck.ExecutionExtendEntry

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def ExtendOutput (original current : Heap) (store : Store Unit) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (result : Option Basis) (values : List Value) : Prop :=
  match result with
  | none => values = basisValues basis rowOwner rowPointer columnOwner columnPointer
  | some next => ∃ rows columns, CandidateBasis original current store next rows columns ∧
      values = basisValues next rows.root rows.root columns.root columns.root

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendReturn_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64)
    (found : Bool) (rows columns value : UInt64)
    (choice : ExtendOuterChoiceLocals locals found rows columns value) (Q : Assertion Unit)
    (next : ∀ frame, frame.values =
      (if found then [.i64 value, .i64 columns, .i64 columns, .i64 rows, .i64 rows]
        else basisValues basis rowOwner rowPointer columnOwner columnPointer) → Q (.Fallthrough initial frame)) :
    wp Project.Beck.«module» (func26.drop 36) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  cases found
  all_goals
    simp only [func26, List.drop]
    repeat' first
      | (wp_run [extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          choice.size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil,
          choice.tag, choice.rowsOwner, choice.rowsPointer, choice.columnsOwner, choice.columnsPointer,
          choice.determinant, choice.extraOwner, Bool.false_eq_true,
          show (1 : UInt64) ≠ 0 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  all_goals exact next _ rfl

#print axioms extendReturn_exact

end Project.Beck.Execution
