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
  | letFlagBefore (input : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) result) :
      Eval (.letE name input.expr a b nondep) values result
  | bindFlagBefore (input : BooleanType) (output : ResultType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) result) : Eval (BooleanWordRange.bind name binder input output a b) values result
  | letWordBefore (input : ResultType) (value : EvalWith a values word)
      (body : Eval b (.word word :: values) result) : Eval (.letE name input.expr a b nondep) values result
  | bindWordBefore (input output : ResultType) (value : EvalWith a values word)
      (body : Eval b (.word word :: values) result) : Eval (Identity.bind name binder a b input output) values result
  | letWordResult (input : ResultType) (value : Eval a values word)
      (body : EvalWith b (.word word :: values) result) : Eval (.letE name input.expr a b nondep) values result
  | bindWordResult (input output : ResultType) (value : Eval a values word)
      (body : EvalWith b (.word word :: values) result) : Eval (Identity.bind name binder a b input output) values result
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
  | letFlagBefore (input : BooleanType)
      (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindFlagBefore (input : BooleanType) (output : ResultType)
      (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) : Supported types (BooleanWordRange.bind name binder input output a b)
  | letWordBefore (input : ResultType) (value : SupportedWith types a)
      (body : Supported (.word :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindWordBefore (input output : ResultType) (value : SupportedWith types a)
      (body : Supported (.word :: types) b) : Supported types (Identity.bind name binder a b input output)
  | letWordResult (input : ResultType) (value : Supported types a)
      (body : SupportedWith (.word :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindWordResult (input output : ResultType) (value : Supported types a)
      (body : SupportedWith (.word :: types) b) : Supported types (Identity.bind name binder a b input output)
  | choice (type : ResultType) (condition : SupportedWith types (BooleanRange.decision test evidence))
      (yesBranch : Supported types yes) (noBranch : Supported types no) :
      Supported types (choiceExpr type test evidence yes no)
  | run (type : ResultType) (body : Supported types source) : Supported types (Identity.run source type)
  | pure (type : ResultType) (body : Supported types source) : Supported types (Identity.pure source type)
  | metadata (body : Supported types source) : Supported types (.mdata data source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ result, Eval source values result := by
  induction supported generalizing values with
  | scalar body =>
    obtain ⟨result, evaluated⟩ := body.evaluates values typed
    exact ⟨result, .scalar evaluated⟩
  | rangeExit body =>
    obtain ⟨result, evaluated⟩ := body.evaluates values typed
    exact ⟨result, .rangeExit evaluated⟩
  | booleanWord body =>
    obtain ⟨result, evaluated⟩ := body.evaluates values typed
    exact ⟨result, .booleanWord evaluated⟩
  | letFlagBefore input value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, continuation⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letFlagBefore input evaluated continuation⟩
  | bindFlagBefore input output value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, continuation⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindFlagBefore input output evaluated continuation⟩
  | letWordBefore input value _ ih =>
    obtain ⟨word, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := ih (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letWordBefore input evaluated continuation⟩
  | bindWordBefore input output value _ ih =>
    obtain ⟨word, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := ih (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindWordBefore input output evaluated continuation⟩
  | letWordResult input _ body ih =>
    obtain ⟨word, evaluated⟩ := ih values typed
    obtain ⟨result, continuation⟩ := body.evaluates (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letWordResult input evaluated continuation⟩
  | bindWordResult input output _ body ih =>
    obtain ⟨word, evaluated⟩ := ih values typed
    obtain ⟨result, continuation⟩ := body.evaluates (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindWordResult input output evaluated continuation⟩
  | choice type condition _ _ yesIH noIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨result, body⟩ := noIH values typed
      exact ⟨result, .choice type evaluated body⟩
    | true =>
      obtain ⟨result, body⟩ := yesIH values typed
      exact ⟨result, .choice type evaluated body⟩
  | run type _ ih =>
    obtain ⟨result, evaluated⟩ := ih values typed
    exact ⟨result, .run type evaluated⟩
  | pure type _ ih =>
    obtain ⟨result, evaluated⟩ := ih values typed
    exact ⟨result, .pure type evaluated⟩
  | metadata _ ih =>
    obtain ⟨result, evaluated⟩ := ih values typed
    exact ⟨result, .metadata evaluated⟩

end LeanExe.Source.Scalar.WordRange
