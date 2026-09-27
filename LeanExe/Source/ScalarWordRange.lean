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
  | letBinaryPredicate (helper : BooleanBinaryHelper)
      (function : ∀ x y, EvalWith (.app (.const ``Bool.toUInt64 []) helper.body)
        (.word y :: .word x :: values) (Bool.toUInt64 (f x y)))
      (body : Eval helper.continuation (.binaryPredicateFunction f :: values) outcome) :
      Eval helper.expr values outcome
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
  | letPredicateFn (expression : Lean.Expr) (type : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) expression)
        (.word x :: values) (Bool.toUInt64 (f x)))
      (body : Eval b (.predicateFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression paramBi) b nondep) values outcome
  | letBooleanPredicateFn (expression : Lean.Expr) (type : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) expression)
        (.boolean x :: values) (Bool.toUInt64 (f x)))
      (body : Eval b (.booleanPredicateFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) expression paramBi) b nondep) values outcome
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
  | letBinaryPredicate (helper : BooleanBinaryHelper)
      (function : SupportedWith (.word :: .word :: types) (.app (.const ``Bool.toUInt64 []) helper.body))
      (body : Supported (.binaryPredicateFunction :: types) helper.continuation) :
      Supported types helper.expr
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
  | letPredicateFn (expression : Lean.Expr) (type : BooleanType)
      (function : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) expression))
      (body : Supported (.predicateFunction :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression paramBi) b nondep)
  | letBooleanPredicateFn (expression : Lean.Expr) (type : BooleanType)
      (function : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) expression))
      (body : Supported (.booleanPredicateFunction :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) expression paramBi) b nondep)
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
  | letBinaryPredicate helper function _ ihb =>
    have total : ∀ x y, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) helper.body) (.word y :: .word x :: values) flag.toUInt64 := by
      intro x y
      obtain ⟨encoded, evaluated⟩ := function.evaluates (.word y :: .word x :: values)
        (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x y => (total x y).choose
    obtain ⟨value, evaluated⟩ := ihb (.binaryPredicateFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBinaryPredicate helper (fun x y => (total x y).choose_spec) evaluated⟩
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
        EvalWith (.app (.const ``Bool.toUInt64 []) expression) (.word x :: values) flag.toUInt64 := by
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
        EvalWith (.app (.const ``Bool.toUInt64 []) expression) (.boolean x :: values) flag.toUInt64 := by
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
