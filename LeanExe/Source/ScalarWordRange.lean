import LeanExe.Source.ScalarBooleanWordRange

namespace LeanExe.Source.Scalar.WordRange

/-- A word-valued conditional with its exact result annotation and decision. -/
def choiceExpr (type : ResultType) (condition evidence yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type.expr) condition) evidence) yes) no

/-- Word computations with at most one dynamically executed range per path. -/
inductive Eval : Lean.Expr → List Value → UInt64 → Prop where
  | scalar (body : EvalWith source values result) : Eval source values result
  | rangeExit (body : Range.Exit.Eval source values result) : Eval source values result
  | booleanWord (body : BooleanWordRange.Eval source values result) : Eval source values result
  | choice (type : ResultType)
      (condition : EvalWith (BooleanRange.decision test evidence) values (Bool.toUInt64 flag))
      (body : Eval (if flag then yes else no) values result) :
      Eval (choiceExpr type test evidence yes no) values result
  | run (type : ResultType) (body : Eval source values result) : Eval (Identity.run source type) values result
  | pure (type : ResultType) (body : Eval source values result) : Eval (Identity.pure source type) values result
  | metadata (body : Eval source values result) : Eval (.mdata data source) values result

inductive Supported : List BindingKind → Lean.Expr → Prop where
  | scalar (body : SupportedWith types source) : Supported types source
  | rangeExit (body : Range.Exit.Supported types source) : Supported types source
  | booleanWord (body : BooleanWordRange.Supported types source) : Supported types source
  | choice (type : ResultType) (condition : SupportedWith types (BooleanRange.decision test evidence))
      (yesBranch : Supported types yes) (noBranch : Supported types no) :
      Supported types (choiceExpr type test evidence yes no)
  | run (type : ResultType) (body : Supported types source) : Supported types (Identity.run source type)
  | pure (type : ResultType) (body : Supported types source) : Supported types (Identity.pure source type)
  | metadata (body : Supported types source) : Supported types (.mdata data source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ result, Eval source values result := by
  induction supported with
  | scalar body =>
    obtain ⟨result, evaluated⟩ := body.evaluates values typed
    exact ⟨result, .scalar evaluated⟩
  | rangeExit body =>
    obtain ⟨result, evaluated⟩ := body.evaluates values typed
    exact ⟨result, .rangeExit evaluated⟩
  | booleanWord body =>
    obtain ⟨result, evaluated⟩ := body.evaluates values typed
    exact ⟨result, .booleanWord evaluated⟩
  | choice type condition _ _ yesIH noIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨result, body⟩ := noIH
      exact ⟨result, .choice type evaluated body⟩
    | true =>
      obtain ⟨result, body⟩ := yesIH
      exact ⟨result, .choice type evaluated body⟩
  | run type _ ih =>
    obtain ⟨result, evaluated⟩ := ih
    exact ⟨result, .run type evaluated⟩
  | pure type _ ih =>
    obtain ⟨result, evaluated⟩ := ih
    exact ⟨result, .pure type evaluated⟩
  | metadata _ ih =>
    obtain ⟨result, evaluated⟩ := ih
    exact ⟨result, .metadata evaluated⟩

end LeanExe.Source.Scalar.WordRange
