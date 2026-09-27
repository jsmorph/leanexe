import Project.Beck.ExecutionBorderEligible
import Project.Beck.ExecutionInputValidate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def borderGuardSaved (saved : BorderSaved) (rowOwner rowPointer columnOwner columnPointer : UInt64)
    (row column : Nat) (k : Fin 30) : Value :=
  match k.val with
  | 0 => .i64 rowOwner
  | 1 => .i64 rowPointer
  | 2 => .i64 row.toUInt64
  | 3 => .i64 columnOwner
  | 4 => .i64 columnPointer
  | 5 => .i64 column.toUInt64
  | _ => saved k

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem borderValidate_exact (env : HostEnv Unit) (initial : Store Unit) (width : Nat)
    (matrixOwner matrixPointer : UInt64) (basis : Basis) (rowOwner rowPointer columnOwner columnPointer : UInt64)
    (row column : Nat) (saved : BorderSaved) (tail : BorderTail)
    (rowsAt : UInt64Array.At initial rowPointer basis.rows) (columnsAt : UInt64Array.At initial columnPointer basis.columns)
    (Q : Assertion Unit)
    (reject : (contains basis.rows row.toUInt64 || contains basis.columns column.toUInt64) = true →
      ∀ frame, BorderResult frame 0 0 0 → Q (.Fallthrough initial frame))
    (accept : contains basis.rows row.toUInt64 = false → contains basis.columns column.toUInt64 = false →
      wp Project.Beck.«module» borderEligible (inputJoin Q) initial
        (borderFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column)
          (borderGuardSaved saved rowOwner rowPointer columnOwner columnPointer row column) tail) env) :
    wp Project.Beck.«module» (func25.take 22) Q initial
      (borderFrame (borderParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer row column) saved tail) env := by
  have rowsCall := contains_exact env initial basis.rows rowOwner rowPointer row.toUInt64 rowsAt
  have columnsCall := contains_exact env initial basis.columns columnOwner columnPointer column.toUInt64 columnsAt
  have shape : func25.take 22 = func25.take 21 ++ [.iff 0 0
      [.constI64 0, .localSet 34, .constI64 0, .localSet 35, .constI64 0, .localSet 36,
        .constI64 0, .localSet 37, .constI64 0, .localSet 38, .constI64 0, .localSet 39] borderEligible] := rfl
  rw [shape]
  generalize codeEq : borderEligible = code
  cases rows : contains basis.rows row.toUInt64 <;> cases columns : contains basis.columns column.toUInt64
  all_goals
    simp only [func25, List.take, List.cons_append, List.nil_append, borderFrame, borderParams, basisValues,
      borderPrefix, borderTail, List.reverse_cons, List.reverse_nil]
    repeat' first
      | (refine wp_call_tw rowsCall ?_; rintro final values ⟨same, rfl⟩; subst final)
      | (refine wp_call_tw columnsCall ?_; rintro final values ⟨same, rfl⟩; subst final)
      | wp_fixed_frame_step
      | ((first | rw [wp_eqI64_cons] | rw [wp_eqz_cons] | rw [wp_const_cons] | rw [wp_nil]) <;>
          simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
            List.take, List.drop, List.append_nil, boolWord, rows, columns, Bool.false_eq_true,
            ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
  all_goals
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
  · rw [← codeEq]
    convert accept rows columns using 2 <;> try rfl
    rename_i cont
    cases cont with
    | Break k st frame => cases k <;> simp [inputJoin, wp_nil]
    | _ => simp [inputJoin, wp_nil]
  all_goals
    wp_fixed_frame [List.take, List.drop, List.append_nil]
    apply reject (by simp [rows, columns])
    constructor <;> rfl

#print axioms borderValidate_exact

end Project.Beck.Execution
