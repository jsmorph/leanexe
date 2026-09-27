import LeanExe.Source.ScalarBooleanRange

namespace LeanExe.Source.Scalar.BooleanWordRange

/-- Standard Id sequencing from a Boolean action to a word continuation. -/
def bind (name : Lean.Name) (binder : Lean.BinderInfo) (input : BooleanType)
    (output : ResultType) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) input.expr) output.expr) value)
    (.lam name input.expr body binder)

/-- A Boolean loop can feed an arbitrary admitted pure word continuation. -/
inductive Eval : Lean.Expr → List Value → UInt64 → Prop where
  | letBinaryFn (type : ResultType)
      (function : ∀ x y, EvalWith a (.word y :: .word x :: values) (f x y))
      (body : Eval b (.binaryFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) values outcome
  | letManyFn (shape : ManyFunction)
      (function : ∀ arguments : List UInt64, arguments.length = shape.arity →
        EvalWith shape.body (arguments.reverse.map Scalar.Value.word ++ values) (f arguments))
      (body : Eval b (.manyFunction shape.arity f :: values) outcome) :
      Eval (shape.bind name b nondep) values outcome
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values) (f x))
      (body : Eval b (.function true f :: values) outcome) :
      Eval (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values outcome
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values) (f x))
      (body : Eval b (.function false f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
  | letBooleanFn (type : ResultType)
      (function : ∀ x, EvalWith a (.boolean x :: values) (f x))
      (body : Eval b (.booleanFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) a paramBi) b nondep) values outcome
  | letPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr)
        (.word x :: values) (Bool.toUInt64 (f x)))
      (body : Eval b (.predicateFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep) values outcome
  | letBooleanPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr)
        (.boolean x :: values) (Bool.toUInt64 (f x)))
      (body : Eval b (.booleanPredicateFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) expression.expr paramBi) b nondep) values outcome
  | idFunctionInput (input result : Lean.Expr)
      (body : Eval (.letE name (.forallE typeName input result typeBi)
        (.lam paramName input value paramBi) tail nondep) values outcome) :
      Eval (.letE name (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
        (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) tail nondep) values outcome
  | letFlagBefore (input : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) result) :
      Eval (.letE name input.expr a b nondep) values result
  | bindFlagBefore (input : BooleanType) (output : ResultType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) result) : Eval (bind name binder input output a b) values result
  | letWordBefore (input : ResultType) (value : EvalWith a values word)
      (body : Eval b (.word word :: values) result) : Eval (.letE name input.expr a b nondep) values result
  | bindWordBefore (input output : ResultType) (value : EvalWith a values word)
      (body : Eval b (.word word :: values) result) : Eval (Identity.bind name binder a b input output) values result
  | letWordResult (input : ResultType) (value : Eval a values word)
      (body : EvalWith b (.word word :: values) result) : Eval (.letE name input.expr a b nondep) values result
  | bindWordResult (input output : ResultType) (value : Eval a values word)
      (body : EvalWith b (.word word :: values) result) : Eval (Identity.bind name binder a b input output) values result
  | letResult (input : BooleanType) (value : BooleanRange.Eval a values flag)
      (body : EvalWith b (.boolean flag :: values) result) :
      Eval (.letE name input.expr a b nondep) values result
  | bindResult (input : BooleanType) (output : ResultType)
      (value : BooleanRange.Eval a values flag) (body : EvalWith b (.boolean flag :: values) result) :
      Eval (bind name binder input output a b) values result
  | converted (value : BooleanRange.Eval source values flag) :
      Eval (.app (.const ``Bool.toUInt64 []) source) values flag.toUInt64
  | run (type : ResultType) (body : Eval source values result) : Eval (Identity.run source type) values result
  | pure (type : ResultType) (body : Eval source values result) : Eval (Identity.pure source type) values result
  | metadata (body : Eval source values result) : Eval (.mdata data source) values result

inductive Supported : List BindingKind → Lean.Expr → Prop where
  | letBinaryFn (type : ResultType) (function : SupportedWith (.word :: .word :: types) a)
      (body : Supported (.binaryFunction :: types) b) :
      Supported types (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)
  | letManyFn (shape : ManyFunction)
      (function : SupportedWith (List.replicate shape.arity .word ++ types) shape.body)
      (body : Supported (.manyFunction shape.arity :: types) b) :
      Supported types (shape.bind name b nondep)
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax) (function : SupportedWith (.word :: .unit :: types) a)
      (body : Supported (.function true :: types) b) :
      Supported types (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | letFn (type : ResultType) (function : SupportedWith (.word :: types) a)
      (body : Supported (.function false :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letBooleanFn (type : ResultType) (function : SupportedWith (.boolean :: types) a)
      (body : Supported (.booleanFunction :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) a paramBi) b nondep)
  | letPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) expression.expr))
      (body : Supported (.predicateFunction :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep)
  | letBooleanPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) expression.expr))
      (body : Supported (.booleanPredicateFunction :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) expression.expr paramBi) b nondep)
  | idFunctionInput (input result : Lean.Expr)
      (body : Supported types (.letE name (.forallE typeName input result typeBi)
        (.lam paramName input value paramBi) tail nondep)) :
      Supported types (.letE name (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
        (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) tail nondep)
  | letFlagBefore (input : BooleanType)
      (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindFlagBefore (input : BooleanType) (output : ResultType)
      (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) : Supported types (bind name binder input output a b)
  | letWordBefore (input : ResultType) (value : SupportedWith types a)
      (body : Supported (.word :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindWordBefore (input output : ResultType) (value : SupportedWith types a)
      (body : Supported (.word :: types) b) : Supported types (Identity.bind name binder a b input output)
  | letWordResult (input : ResultType) (value : Supported types a)
      (body : SupportedWith (.word :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindWordResult (input output : ResultType) (value : Supported types a)
      (body : SupportedWith (.word :: types) b) : Supported types (Identity.bind name binder a b input output)
  | letResult (input : BooleanType) (value : BooleanRange.Supported types a)
      (body : SupportedWith (.boolean :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindResult (input : BooleanType) (output : ResultType)
      (value : BooleanRange.Supported types a) (body : SupportedWith (.boolean :: types) b) :
      Supported types (bind name binder input output a b)
  | converted (value : BooleanRange.Supported types source) :
      Supported types (.app (.const ``Bool.toUInt64 []) source)
  | run (type : ResultType) (body : Supported types source) : Supported types (Identity.run source type)
  | pure (type : ResultType) (body : Supported types source) : Supported types (Identity.pure source type)
  | metadata (body : Supported types source) : Supported types (.mdata data source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ result, Eval source values result := by
  induction supported generalizing values with
  | letBinaryFn type function _ ihb =>
    have total := fun x y => function.evaluates (.word y :: .word x :: values) (by simp [Value.kind, typed])
    let f := fun x y => (total x y).choose
    obtain ⟨value, hv⟩ := ihb (.binaryFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBinaryFn type (fun x y => (total x y).choose_spec) hv⟩
  | letManyFn shape function _ ihb =>
    obtain ⟨f, meanings⟩ := function.manyFunction_evaluates values typed
    obtain ⟨value, evaluated⟩ := ihb (.manyFunction shape.arity f :: values)
      (by simp [Scalar.Value.kind, typed])
    exact ⟨value, .letManyFn shape meanings evaluated⟩
  | letUnitFn type unitForm function _ ihb =>
    have total := fun x => function.evaluates (.word x :: .unit :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function true f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letUnitFn type unitForm (fun x => (total x).choose_spec) hv⟩
  | letFn type function _ ihb =>
    have total := fun x => function.evaluates (.word x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letFn type (fun x => (total x).choose_spec) hv⟩
  | letBooleanFn type function _ ihb =>
    have total := fun x => function.evaluates (.boolean x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.booleanFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBooleanFn type (fun x => (total x).choose_spec) hv⟩
  | letPredicateFn expression type function _ ih =>
    have total : ∀ x : UInt64, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.word x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := function.evaluates (.word x :: values) (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.predicateFunction f :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letPredicateFn expression type (fun x => (total x).choose_spec) evaluated⟩
  | letBooleanPredicateFn expression type function _ ih =>
    have total : ∀ x : Bool, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.boolean x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := function.evaluates (.boolean x :: values) (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.booleanPredicateFunction f :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letBooleanPredicateFn expression type (fun x => (total x).choose_spec) evaluated⟩
  | idFunctionInput input result _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .idFunctionInput input result evaluated⟩
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
  | letResult input value body =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := body.evaluates (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letResult input evaluated continuation⟩
  | bindResult input output value body =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := body.evaluates (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindResult input output evaluated continuation⟩
  | converted value =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    exact ⟨flag.toUInt64, .converted evaluated⟩
  | run type _ ih => obtain ⟨result, evaluated⟩ := ih values typed; exact ⟨result, .run type evaluated⟩
  | pure type _ ih => obtain ⟨result, evaluated⟩ := ih values typed; exact ⟨result, .pure type evaluated⟩
  | metadata _ ih => obtain ⟨result, evaluated⟩ := ih values typed; exact ⟨result, .metadata evaluated⟩

end LeanExe.Source.Scalar.BooleanWordRange
