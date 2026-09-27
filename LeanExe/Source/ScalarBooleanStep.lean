import LeanExe.Source.Scalar
import LeanExe.Source.ScalarBooleanIteration

namespace LeanExe.Source.Scalar.BooleanStep

def resultType : BooleanType → Lean.Expr
  | .boolean => .app (.const ``ForInStep [.zero]) (.const ``Bool [])
  | .identity inner => .app (.const ``Id [.zero]) (resultType inner)

def yieldDirect (value : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``ForInStep.yield [.zero]) (.const ``Bool [])) value

def doneDirect (value : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``ForInStep.done [.zero]) (.const ``Bool [])) value

def idRun (type : BooleanType) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``Id.run [.zero]) (resultType type)) body

def idPure (type : BooleanType) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero])))) (resultType type)) body

def choiceExpr (type : BooleanType) (condition evidence yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (resultType type)) condition) evidence) yes) no

def decision (condition evidence : Lean.Expr) : Lean.Expr :=
  .app (.const ``Bool.toUInt64 []) (.app (.app (.const ``Decidable.decide []) condition) evidence)

/-- Native Boolean step results retain their yield/done distinction. -/
inductive Eval : Lean.Expr → List Value → ForInStep Bool → Prop where
  | yieldDirect (value : EvalWith (.app (.const ``Bool.toUInt64 []) source) values (Bool.toUInt64 flag)) :
      Eval (yieldDirect source) values (.yield flag)
  | doneDirect (value : EvalWith (.app (.const ``Bool.toUInt64 []) source) values (Bool.toUInt64 flag)) :
      Eval (doneDirect source) values (.done flag)
  | idRun (type : BooleanType) (body : Eval source values outcome) : Eval (idRun type source) values outcome
  | idPure (type : BooleanType) (body : Eval source values outcome) : Eval (idPure type source) values outcome
  | metadata (body : Eval source values outcome) : Eval (.mdata data source) values outcome
  | choose (type : BooleanType)
      (condition : EvalWith (decision test evidence) values (Bool.toUInt64 flag))
      (body : Eval (if flag then yes else no) values outcome) :
      Eval (choiceExpr type test evidence yes no) values outcome
  | letWord (type : ResultType) (value : EvalWith a values x)
      (body : Eval b (.word x :: values) outcome) :
      Eval (.letE name type.expr a b nondep) values outcome
  | letBoolean (type : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) outcome) :
      Eval (.letE name type.expr a b nondep) values outcome

/-- Support checks both branches and every bound value, including unused ones. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | yieldDirect (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) source)) :
      Supported types (yieldDirect source)
  | doneDirect (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) source)) :
      Supported types (doneDirect source)
  | idRun (type : BooleanType) (body : Supported types source) : Supported types (idRun type source)
  | idPure (type : BooleanType) (body : Supported types source) : Supported types (idPure type source)
  | metadata (body : Supported types source) : Supported types (.mdata data source)
  | choose (type : BooleanType) (condition : SupportedWith types (decision test evidence))
      (first : Supported types yes) (second : Supported types no) :
      Supported types (choiceExpr type test evidence yes no)
  | letWord (type : ResultType) (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (.letE name type.expr a b nondep)
  | letBoolean (type : BooleanType) (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) : Supported types (.letE name type.expr a b nondep)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ outcome, Eval source values outcome := by
  induction supported generalizing values with
  | yieldDirect value =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨.yield flag, .yieldDirect evaluated⟩
  | doneDirect value =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨.done flag, .doneDirect evaluated⟩
  | idRun type _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .idRun type evaluated⟩
  | idPure type _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .idPure type evaluated⟩
  | metadata _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .metadata evaluated⟩
  | choose type condition _ _ yesIH noIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨outcome, body⟩ := noIH values typed
      exact ⟨outcome, .choose type evaluated body⟩
    | true =>
      obtain ⟨outcome, body⟩ := yesIH values typed
      exact ⟨outcome, .choose type evaluated body⟩
  | letWord type value _ ih =>
    obtain ⟨x, evaluated⟩ := value.evaluates values typed
    obtain ⟨outcome, body⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letWord type evaluated body⟩
  | letBoolean type value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨outcome, body⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letBoolean type evaluated body⟩

end LeanExe.Source.Scalar.BooleanStep
