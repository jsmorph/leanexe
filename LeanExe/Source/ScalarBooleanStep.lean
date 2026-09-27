import LeanExe.Source.Scalar
import LeanExe.Source.ScalarBooleanIteration
import LeanExe.Source.ScalarBooleanStepValues

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

def bindExpr (input : Lean.Expr) (output : BooleanType) (name : Lean.Name)
    (bi : Lean.BinderInfo) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) input) (resultType output)) value)
    (.lam name input body bi)

def functionExpr (input : Lean.Expr) (output : BooleanType)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (value body : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE name (.forallE typeName input (resultType output) typeBi)
    (.lam paramName input value paramBi) body nondep

/-- Native Boolean step results retain their yield/done distinction. -/
inductive Eval : Lean.Expr → List Value → ForInStep Bool → Prop where
  | yieldDirect (value : EvalWith (.app (.const ``Bool.toUInt64 []) source) (values.map Value.toScalar) (Bool.toUInt64 flag)) :
      Eval (yieldDirect source) values (.yield flag)
  | doneDirect (value : EvalWith (.app (.const ``Bool.toUInt64 []) source) (values.map Value.toScalar) (Bool.toUInt64 flag)) :
      Eval (doneDirect source) values (.done flag)
  | idRun (type : BooleanType) (body : Eval source values outcome) : Eval (idRun type source) values outcome
  | idPure (type : BooleanType) (body : Eval source values outcome) : Eval (idPure type source) values outcome
  | metadata (body : Eval source values outcome) : Eval (.mdata data source) values outcome
  | choose (type : BooleanType)
      (condition : EvalWith (decision test evidence) (values.map Value.toScalar) (Bool.toUInt64 flag))
      (body : Eval (if flag then yes else no) values outcome) :
      Eval (choiceExpr type test evidence yes no) values outcome
  | letWord (type : ResultType) (value : EvalWith a (values.map Value.toScalar) x)
      (body : Eval b (.scalar (.word x) :: values) outcome) :
      Eval (.letE name type.expr a b nondep) values outcome
  | letBoolean (type : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) (values.map Value.toScalar) (Bool.toUInt64 flag))
      (body : Eval b (.scalar (.boolean flag) :: values) outcome) :
      Eval (.letE name type.expr a b nondep) values outcome
  | bindWord (input : ResultType) (output : BooleanType) (value : EvalWith a (values.map Value.toScalar) x)
      (body : Eval b (.scalar (.word x) :: values) outcome) :
      Eval (bindExpr input.expr output name bi a b) values outcome
  | bindBoolean (input output : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) (values.map Value.toScalar) (Bool.toUInt64 flag))
      (body : Eval b (.scalar (.boolean flag) :: values) outcome) :
      Eval (bindExpr input.expr output name bi a b) values outcome

  | letWordFunction (input : ResultType) (output : BooleanType)
      (function : ∀ x, Eval a (.scalar (.word x) :: values) (f x))
      (body : Eval b (.wordFunction f :: values) outcome) :
      Eval (functionExpr input.expr output name typeName paramName typeBi paramBi a b nondep) values outcome
  | letBooleanFunction (input output : BooleanType)
      (function : ∀ x, Eval a (.scalar (.boolean x) :: values) (f x))
      (body : Eval b (.booleanFunction f :: values) outcome) :
      Eval (functionExpr input.expr output name typeName paramName typeBi paramBi a b nondep) values outcome
  | wordApply (function : values[index]? = some (.wordFunction f))
      (argument : EvalWith a (values.map Value.toScalar) x) :
      Eval (.app (.bvar index) a) values (f x)
  | booleanApply (function : values[index]? = some (.booleanFunction f))
      (argument : EvalWith (.app (.const ``Bool.toUInt64 []) a) (values.map Value.toScalar) (Bool.toUInt64 flag)) :
      Eval (.app (.bvar index) a) values (f flag)

/-- Support checks both branches and every bound value, including unused ones. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | yieldDirect (value : SupportedWith (types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) source)) :
      Supported types (yieldDirect source)
  | doneDirect (value : SupportedWith (types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) source)) :
      Supported types (doneDirect source)
  | idRun (type : BooleanType) (body : Supported types source) : Supported types (idRun type source)
  | idPure (type : BooleanType) (body : Supported types source) : Supported types (idPure type source)
  | metadata (body : Supported types source) : Supported types (.mdata data source)
  | choose (type : BooleanType) (condition : SupportedWith (types.map BindingKind.toScalar) (decision test evidence))
      (first : Supported types yes) (second : Supported types no) :
      Supported types (choiceExpr type test evidence yes no)
  | letWord (type : ResultType) (value : SupportedWith (types.map BindingKind.toScalar) a) (body : Supported (.scalar .word :: types) b) :
      Supported types (.letE name type.expr a b nondep)
  | letBoolean (type : BooleanType) (value : SupportedWith (types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.scalar .boolean :: types) b) : Supported types (.letE name type.expr a b nondep)

  | bindWord (input : ResultType) (output : BooleanType) (value : SupportedWith (types.map BindingKind.toScalar) a)
      (body : Supported (.scalar .word :: types) b) :
      Supported types (bindExpr input.expr output name bi a b)
  | bindBoolean (input output : BooleanType)
      (value : SupportedWith (types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.scalar .boolean :: types) b) :
      Supported types (bindExpr input.expr output name bi a b)

  | letWordFunction (input : ResultType) (output : BooleanType)
      (function : Supported (.scalar .word :: types) a)
      (body : Supported (.wordFunction :: types) b) :
      Supported types (functionExpr input.expr output name typeName paramName typeBi paramBi a b nondep)
  | letBooleanFunction (input output : BooleanType)
      (function : Supported (.scalar .boolean :: types) a)
      (body : Supported (.booleanFunction :: types) b) :
      Supported types (functionExpr input.expr output name typeName paramName typeBi paramBi a b nondep)
  | wordApply (function : types[index]? = some .wordFunction)
      (argument : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (.app (.bvar index) a)
  | booleanApply (function : types[index]? = some .booleanFunction)
      (argument : SupportedWith (types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) a)) :
      Supported types (.app (.bvar index) a)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ outcome, Eval source values outcome := by
  classical
  induction supported generalizing values with
  | yieldDirect value =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨.yield flag, .yieldDirect evaluated⟩
  | doneDirect value =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
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
    obtain ⟨encoded, evaluated⟩ := condition.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨outcome, body⟩ := noIH values typed
      exact ⟨outcome, .choose type evaluated body⟩
    | true =>
      obtain ⟨outcome, body⟩ := yesIH values typed
      exact ⟨outcome, .choose type evaluated body⟩
  | letWord type value _ ih =>
    obtain ⟨x, evaluated⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, body⟩ := ih (.scalar (.word x) :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letWord type evaluated body⟩
  | letBoolean type value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨outcome, body⟩ := ih (.scalar (.boolean flag) :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letBoolean type evaluated body⟩
  | bindWord input output value _ ih =>
    obtain ⟨x, evaluated⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, body⟩ := ih (.scalar (.word x) :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .bindWord input output evaluated body⟩
  | bindBoolean input output value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨outcome, body⟩ := ih (.scalar (.boolean flag) :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .bindBoolean input output evaluated body⟩
  | letWordFunction input output _ _ ihf ihb =>
    have total := fun x => ihf (.scalar (.word x) :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.wordFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letWordFunction input output (fun x => (total x).choose_spec) evaluated⟩
  | letBooleanFunction input output _ _ ihf ihb =>
    have total := fun x => ihf (.scalar (.boolean x) :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.booleanFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letBooleanFunction input output (fun x => (total x).choose_spec) evaluated⟩
  | wordApply present argument =>
    obtain ⟨f, found⟩ := wordFunction_lookup typed present
    obtain ⟨x, evaluated⟩ := argument.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨f x, .wordApply found evaluated⟩
  | booleanApply present argument =>
    obtain ⟨f, found⟩ := booleanFunction_lookup typed present
    obtain ⟨encoded, evaluated⟩ := argument.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨f flag, .booleanApply found evaluated⟩

end LeanExe.Source.Scalar.BooleanStep
