import LeanExe.Source.Scalar
import LeanExe.Source.ScalarStepValues
import LeanExe.Source.ScalarStepSyntax

namespace LeanExe.Source.Scalar.Step

/-- Native yielding/done behavior of a checked scalar loop body. Scalar and
step-valued closures have distinct bindings and keep their captured values. -/
inductive Eval : Lean.Expr → List Value → ForInStep UInt64 → Prop where
  | yieldValue (value : EvalWith a (values.map Value.toScalar) x) :
      Eval (Range.yieldValue a) values (.yield x)
  | doneValue (value : EvalWith a (values.map Value.toScalar) x) :
      Eval (doneValue a) values (.done x)
  | choose (op : Comparison) (type : ResultType)
      (left : EvalWith a (values.map Value.toScalar) x) (right : EvalWith b (values.map Value.toScalar) y)
      (chosen : Eval (if op.denote x y then onTrue else onFalse) values outcome) :
      Eval (branch op type a b onTrue onFalse) values outcome
  | letE (value : EvalWith a (values.map Value.toScalar) x)
      (body : Eval b (.scalar (.word x) :: values) outcome) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values outcome
  | idBind (value : EvalWith a (values.map Value.toScalar) x)
      (body : Eval b (.scalar (.word x) :: values) outcome) :
      Eval (Range.bindYield name bi a b) values outcome
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values.map Value.toScalar) (f x))
      (body : Eval b (.scalar (.function false f) :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
  | letUnitFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values.map Value.toScalar) (f x))
      (body : Eval b (.scalar (.function true f) :: values) outcome) :
      Eval (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values outcome
  | apply (function : values[index]? = some (.function false f))
      (argument : EvalWith a (values.map Value.toScalar) x) :
      Eval (.app (.bvar index) a) values (f x)
  | unitApply (function : values[index]? = some (.function true f))
      (argument : EvalWith a (values.map Value.toScalar) x) :
      Eval (.app (.app (.bvar index) (.const ``Unit.unit [])) a) values (f x)
  | letStepFn (type : ResultType)
      (function : ∀ x, Eval a (.scalar (.word x) :: values) (f x))
      (body : Eval b (.function false f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
  | letUnitStepFn (type : ResultType)
      (function : ∀ x, Eval a (.scalar (.word x) :: .scalar .unit :: values) (f x))
      (body : Eval b (.function true f :: values) outcome) :
      Eval (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values outcome
  | metadata (body : Eval a values outcome) : Eval (.mdata data a) values outcome

/-- Independent source support for a body returning ForInStep UInt64.
Every scalar subterm uses the ordinary scalar grammar; step functions are
available only through step calls, never as scalar-valued functions. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | yieldValue (value : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (Range.yieldValue a)
  | doneValue (value : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (doneValue a)
  | choose (op : Comparison) (type : ResultType)
      (left : SupportedWith (types.map BindingKind.toScalar) a)
      (right : SupportedWith (types.map BindingKind.toScalar) b)
      (onTrue : Supported types t) (onFalse : Supported types e) :
      Supported types (branch op type a b t e)
  | letE (value : SupportedWith (types.map BindingKind.toScalar) a)
      (body : Supported (.scalar .word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | idBind (value : SupportedWith (types.map BindingKind.toScalar) a)
      (body : Supported (.scalar .word :: types) b) :
      Supported types (Range.bindYield name bi a b)
  | letFn (type : ResultType)
      (function : SupportedWith (.word :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar (.function false) :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letUnitFn (type : ResultType)
      (function : SupportedWith (.word :: .unit :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar (.function true) :: types) b) :
      Supported types (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | apply (function : types[index]? = some (.function false))
      (argument : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (.app (.bvar index) a)
  | unitApply (function : types[index]? = some (.function true))
      (argument : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (.app (.app (.bvar index) (.const ``Unit.unit [])) a)
  | letStepFn (type : ResultType) (function : Supported (.scalar .word :: types) a)
      (body : Supported (.function false :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letUnitStepFn (type : ResultType)
      (function : Supported (.scalar .word :: .scalar .unit :: types) a)
      (body : Supported (.function true :: types) b) :
      Supported types (.letE name
        (.forallE unitTypeName (.const ``Unit [])
          (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi) unitTypeBi)
        (.lam unitName (.const ``Unit [])
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | metadata (body : Supported types e) : Supported types (.mdata data e)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ outcome, Eval source values outcome := by
  classical
  induction supported generalizing values with
  | yieldValue value =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨.yield x, .yieldValue hx⟩
  | doneValue value =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨.done x, .doneValue hx⟩
  | choose op type left right _ _ it ie =>
    obtain ⟨x, hx⟩ := left.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨y, hy⟩ := right.evaluates (values.map Value.toScalar) (typed_projection typed)
    cases flag : op.denote x y with
    | false =>
      obtain ⟨outcome, evaluated⟩ := ie values typed
      exact ⟨outcome, .choose op type hx hy (by simpa [flag] using evaluated)⟩
    | true =>
      obtain ⟨outcome, evaluated⟩ := it values typed
      exact ⟨outcome, .choose op type hx hy (by simpa [flag] using evaluated)⟩
  | letE value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.word x) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letE hx evaluated⟩
  | idBind value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.word x) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .idBind hx evaluated⟩
  | letFn type function _ ih =>
    have total := fun x => function.evaluates (.word x :: values.map Value.toScalar)
      (by simpa [LeanExe.Source.Scalar.Value.kind] using typed_projection typed)
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.function false f) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letFn type (fun x => (total x).choose_spec) evaluated⟩
  | letUnitFn type function _ ih =>
    have total := fun x => function.evaluates (.word x :: .unit :: values.map Value.toScalar)
      (by simpa [LeanExe.Source.Scalar.Value.kind] using typed_projection typed)
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.function true f) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letUnitFn type (fun x => (total x).choose_spec) evaluated⟩
  | apply present argument =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := argument.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨f x, .apply hf hx⟩
  | unitApply present argument =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := argument.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨f x, .unitApply hf hx⟩
  | letStepFn type _ _ ihf ihb =>
    have total := fun x => ihf (.scalar (.word x) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.function false f :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letStepFn type (fun x => (total x).choose_spec) evaluated⟩
  | letUnitStepFn type _ _ ihf ihb =>
    have total := fun x => ihf (.scalar (.word x) :: .scalar .unit :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.function true f :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letUnitStepFn type (fun x => (total x).choose_spec) evaluated⟩
  | metadata _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .metadata evaluated⟩

end LeanExe.Source.Scalar.Step
