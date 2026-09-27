import LeanExe.IR.ScalarSemantics

namespace LeanExe.IR

/-- Allocating later locals preserves a checked write and leaves the suffix intact. -/
theorem ScalarStore.write_append {store next : ScalarStore} {index : Nat} {value : UInt64}
    (written : store.write index value = some next) (suffix : ScalarStore) :
    (store ++ suffix).write index value = some (next ++ suffix) := by
  unfold ScalarStore.write at written ⊢
  split at written
  · rename_i bound
    cases written
    have extended : index < (store ++ suffix).length := by
      simp only [List.length_append]
      omega
    simp only [extended, ite_true, List.set_append_left index value bound]
  · contradiction

mutual
  /-- Expression evaluation preserves any newly allocated local suffix. -/
  theorem Expr.ScalarEval.append {expression : Expr} {store next : ScalarStore} {value : UInt64}
      (evaluated : expression.ScalarEval store value next) (suffix : ScalarStore) :
      expression.ScalarEval (store ++ suffix) value (next ++ suffix) := by
    cases evaluated with
    | «local» present => exact .local (by simp [List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1, present])
    | const => exact .const
    | bin left right op => exact .bin (left.append suffix) (right.append suffix) op
    | iteTrue condition branch => exact .iteTrue (condition.append suffix) (branch.append suffix)
    | iteFalse condition branch => exact .iteFalse (condition.append suffix) (branch.append suffix)
    | letE value write body => exact .letE (value.append suffix) (ScalarStore.write_append write suffix) (body.append suffix)

  /-- Condition evaluation preserves any newly allocated local suffix. -/
  theorem Cond.ScalarEval.append {condition : Cond} {store next : ScalarStore} {value : Bool}
      (evaluated : condition.ScalarEval store value next) (suffix : ScalarStore) :
      condition.ScalarEval (store ++ suffix) value (next ++ suffix) := by
    cases evaluated with
    | true => exact .true
    | false => exact .false
    | eq left right => exact .eq (left.append suffix) (right.append suffix)
    | lt left right => exact .lt (left.append suffix) (right.append suffix)
    | le left right => exact .le (left.append suffix) (right.append suffix)
    | not inner => exact .not (inner.append suffix)
    | andTrue left right => exact .andTrue (left.append suffix) (right.append suffix)
    | andFalse left => exact .andFalse (left.append suffix)
    | orTrue left => exact .orTrue (left.append suffix)
    | orFalse left right => exact .orFalse (left.append suffix) (right.append suffix)
end

/-- Every terminating scalar statement preserves newly allocated later locals. -/
theorem Stmt.ScalarEval.append {statement : Stmt} {store next : ScalarStore}
    (evaluated : statement.ScalarEval store next) (suffix : ScalarStore) :
    statement.ScalarEval (store ++ suffix) (next ++ suffix) := by
  induction evaluated with
  | skip => exact .skip
  | assign value write => exact .assign (value.append suffix) (ScalarStore.write_append write suffix)
  | seq _ _ first second => exact .seq first second
  | iteTrue condition _ branch => exact .iteTrue (condition.append suffix) branch
  | iteFalse condition _ branch => exact .iteFalse (condition.append suffix) branch
  | whileFalse condition => exact .whileFalse (condition.append suffix)
  | whileTrue condition _ _ body rest => exact .whileTrue (condition.append suffix) body rest

end LeanExe.IR
