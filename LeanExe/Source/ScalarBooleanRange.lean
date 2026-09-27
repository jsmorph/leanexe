import LeanExe.Source.ScalarRangeExitSupported
import LeanExe.Source.ScalarBooleanLet
import LeanExe.Source.ScalarBooleanFunctionChoice
import LeanExe.Source.ScalarBooleanAccumulator

namespace LeanExe.Source.Scalar.BooleanRange

/-- Standard Id sequencing retains its input and Boolean result annotations. -/
def bind (name : Lean.Name) (binder : Lean.BinderInfo) (input : ResultType)
    (output : BooleanType) (value body : Lean.Expr) : Lean.Expr :=
  (BooleanBindingForm.monadic binder output).expr name input.expr value body

def bindBoolean (name : Lean.Name) (binder : Lean.BinderInfo) (input output : BooleanType)
    (value body : Lean.Expr) : Lean.Expr :=
  (BooleanBindingForm.monadic binder output).expr name input.expr value body

/-- Convert an exactly checked proposition decision to its Boolean word value. -/
def decision (condition evidence : Lean.Expr) : Lean.Expr :=
  .app (.const ``Bool.toUInt64 [])
    (.app (.app (.const ``Decidable.decide []) condition) evidence)

def choiceExpr (type : BooleanType) (condition evidence yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type.expr) condition) evidence) yes) no

/-- Boolean programs compose pure scalar computations and bounded word loops. -/
inductive Eval : Lean.Expr → List Value → Bool → Prop where
  | scalar (body : EvalWith (.app (.const ``Bool.toUInt64 []) source) values flag.toUInt64) :
      Eval source values flag
  | accumulator (body : BooleanAccumulator.Eval source values flag) : Eval source values flag
  | wordFunctionChoice (shape : BooleanFunctionBinding) (choice : BooleanFunctionChoice)
      (condition : EvalWith (decision choice.condition choice.evidence) values (Bool.toUInt64 flag))
      (branch : Eval (shape.bodyExpr parameterName (.const ``UInt64 []) value
        (if flag then choice.yes else choice.no)) values result) :
      Eval (shape.bodyExpr parameterName (.const ``UInt64 []) value choice.expr) values result
  | booleanFunctionChoice (shape : BooleanFunctionBinding) (choice : BooleanFunctionChoice)
      (condition : EvalWith (decision choice.condition choice.evidence) values (Bool.toUInt64 flag))
      (branch : Eval (shape.bodyExpr parameterName (.const ``Bool []) value
        (if flag then choice.yes else choice.no)) values result) :
      Eval (shape.bodyExpr parameterName (.const ``Bool []) value choice.expr) values result
  | applyWord (shape : BooleanFunctionBinding) (call : BooleanCall false)
      (argument : EvalWith a values x) (body : Eval b (.word x :: values) result) :
      Eval (shape.callExpr call parameterName (.const ``UInt64 []) a b) values result
  | applyBoolean (shape : BooleanFunctionBinding) (call : BooleanCall true)
      (argument : EvalWith (.app (.const ``Bool.toUInt64 []) a) values flag.toUInt64)
      (body : Eval b (.boolean flag :: values) result) :
      Eval (shape.callExpr call parameterName (.const ``Bool []) a b) values result
  | choice (type : BooleanType)
      (condition : EvalWith (decision test evidence) values (Bool.toUInt64 flag))
      (body : Eval (if flag then yes else no) values result) :
      Eval (choiceExpr type test evidence yes no) values result
  | choiceScalar (type : BooleanType)
      (condition : EvalWith (decision test evidence) values (Bool.toUInt64 flag))
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) (if flag then yes else no)) values (Bool.toUInt64 result)) :
      Eval (choiceExpr type test evidence yes no) values result
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
  | letFlagResult (value : Eval a values flag)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.boolean flag :: values) (Bool.toUInt64 result)) :
      Eval (.letE name (.const ``Bool []) a b nondep) values result
  | bindFlagResult (input output : BooleanType) (value : Eval a values flag)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.boolean flag :: values) (Bool.toUInt64 result)) :
      Eval (bindBoolean name binder input output a b) values result
  | letFlagBefore (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values flag.toUInt64)
      (body : Eval b (.boolean flag :: values) result) :
      Eval (.letE name (.const ``Bool []) a b nondep) values result
  | bindFlagBefore (input output : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values flag.toUInt64)
      (body : Eval b (.boolean flag :: values) result) :
      Eval (bindBoolean name binder input output a b) values result
  | letBefore (value : EvalWith a values x) (body : Eval b (.word x :: values) flag) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values flag
  | bindBefore (input : ResultType) (output : BooleanType)
      (value : EvalWith a values x) (body : Eval b (.word x :: values) flag) :
      Eval (bind name binder input output a b) values flag
  | letResult (value : Range.Exit.Eval a values x)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.word x :: values) flag.toUInt64) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values flag
  | bindResult (input : ResultType) (output : BooleanType)
      (value : Range.Exit.Eval a values x)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.word x :: values) flag.toUInt64) :
      Eval (bind name binder input output a b) values flag
  | idFunctionInput (input result : Lean.Expr)
      (body : Eval (.letE name (.forallE typeName input result typeBi)
        (.lam paramName input value paramBi) tail nondep) values outcome) :
      Eval (.letE name (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
        (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) tail nondep) values outcome
  | idLet (type : Lean.Expr)
      (body : Eval (.letE name type value tail nondep) values result) :
      Eval (.letE name (.app (.const ``Id [.zero]) type) value tail nondep) values result
  | wrapped (wrapper : BooleanWrapper) (body : Eval source values flag) :
      Eval (wrapper.expr source) values flag

/-- Source support checks every helper, scalar expression and loop continuation. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | scalar (body : SupportedWith types (.app (.const ``Bool.toUInt64 []) source)) :
      Supported types source
  | accumulator (body : BooleanAccumulator.Supported types source) : Supported types source
  | wordFunctionChoice (shape : BooleanFunctionBinding) (choice : BooleanFunctionChoice)
      (condition : SupportedWith types (decision choice.condition choice.evidence))
      (yesBranch : Supported types (shape.bodyExpr parameterName (.const ``UInt64 []) value choice.yes))
      (noBranch : Supported types (shape.bodyExpr parameterName (.const ``UInt64 []) value choice.no)) :
      Supported types (shape.bodyExpr parameterName (.const ``UInt64 []) value choice.expr)
  | booleanFunctionChoice (shape : BooleanFunctionBinding) (choice : BooleanFunctionChoice)
      (condition : SupportedWith types (decision choice.condition choice.evidence))
      (yesBranch : Supported types (shape.bodyExpr parameterName (.const ``Bool []) value choice.yes))
      (noBranch : Supported types (shape.bodyExpr parameterName (.const ``Bool []) value choice.no)) :
      Supported types (shape.bodyExpr parameterName (.const ``Bool []) value choice.expr)
  | applyWord (shape : BooleanFunctionBinding) (call : BooleanCall false)
      (argument : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (shape.callExpr call parameterName (.const ``UInt64 []) a b)
  | applyBoolean (shape : BooleanFunctionBinding) (call : BooleanCall true)
      (argument : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) :
      Supported types (shape.callExpr call parameterName (.const ``Bool []) a b)
  | choice (type : BooleanType) (condition : SupportedWith types (decision test evidence))
      (yesBranch : Supported types yes) (noBranch : Supported types no) :
      Supported types (choiceExpr type test evidence yes no)
  | choiceScalarLeft (type : BooleanType) (condition : SupportedWith types (decision test evidence))
      (yesBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) yes)) (noBranch : Supported types no) :
      Supported types (choiceExpr type test evidence yes no)
  | choiceScalarRight (type : BooleanType) (condition : SupportedWith types (decision test evidence))
      (yesBranch : Supported types yes) (noBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) no)) :
      Supported types (choiceExpr type test evidence yes no)
  | choiceScalars (type : BooleanType) (condition : SupportedWith types (decision test evidence))
      (yesBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) yes))
      (noBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) no)) :
      Supported types (choiceExpr type test evidence yes no)
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
  | letFlagResult (value : Supported types a)
      (body : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (.letE name (.const ``Bool []) a b nondep)
  | bindFlagResult (input output : BooleanType) (value : Supported types a)
      (body : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (bindBoolean name binder input output a b)
  | letFlagBefore (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) :
      Supported types (.letE name (.const ``Bool []) a b nondep)
  | bindFlagBefore (input output : BooleanType)
      (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) :
      Supported types (bindBoolean name binder input output a b)
  | letBefore (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | bindBefore (input : ResultType) (output : BooleanType)
      (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (bind name binder input output a b)
  | letResult (value : Range.Exit.Supported types a)
      (body : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | bindResult (input : ResultType) (output : BooleanType)
      (value : Range.Exit.Supported types a)
      (body : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (bind name binder input output a b)
  | idFunctionInput (input result : Lean.Expr)
      (body : Supported types (.letE name (.forallE typeName input result typeBi)
        (.lam paramName input value paramBi) tail nondep)) :
      Supported types (.letE name (.forallE typeName (.app (.const ``Id [.zero]) input) result typeBi)
        (.lam paramName (.app (.const ``Id [.zero]) input) value paramBi) tail nondep)
  | idLet (type : Lean.Expr)
      (body : Supported types (.letE name type value tail nondep)) :
      Supported types (.letE name (.app (.const ``Id [.zero]) type) value tail nondep)
  | wrapped (wrapper : BooleanWrapper) (body : Supported types source) :
      Supported types (wrapper.expr source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ flag, Eval source values flag := by
  induction supported generalizing values with
  | scalar body =>
    obtain ⟨encoded, evaluated⟩ := body.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨flag, .scalar evaluated⟩
  | accumulator body =>
    obtain ⟨flag, evaluated⟩ := body.evaluates values typed
    exact ⟨flag, .accumulator evaluated⟩
  | wordFunctionChoice shape choice condition _ _ yesIH noIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨result, branch⟩ := noIH values typed
      exact ⟨result, .wordFunctionChoice shape choice evaluated branch⟩
    | true =>
      obtain ⟨result, branch⟩ := yesIH values typed
      exact ⟨result, .wordFunctionChoice shape choice evaluated branch⟩
  | booleanFunctionChoice shape choice condition _ _ yesIH noIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨result, branch⟩ := noIH values typed
      exact ⟨result, .booleanFunctionChoice shape choice evaluated branch⟩
    | true =>
      obtain ⟨result, branch⟩ := yesIH values typed
      exact ⟨result, .booleanFunctionChoice shape choice evaluated branch⟩
  | applyWord shape call argument _ ih =>
    obtain ⟨x, hx⟩ := argument.evaluates values typed
    obtain ⟨result, body⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨result, .applyWord shape call hx body⟩
  | applyBoolean shape call argument _ ih =>
    obtain ⟨encoded, evaluated⟩ := argument.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, body⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .applyBoolean shape call evaluated body⟩
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
  | choiceScalarLeft type condition scalar _ noIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨result, body⟩ := noIH values typed
      exact ⟨result, .choice type evaluated body⟩
    | true =>
      obtain ⟨encoded, body⟩ := scalar.evaluates values typed
      obtain ⟨result, rfl⟩ := body.booleanConversion_result
      exact ⟨result, .choiceScalar type evaluated body⟩
  | choiceScalarRight type condition _ scalar yesIH =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨encoded, body⟩ := scalar.evaluates values typed
      obtain ⟨result, rfl⟩ := body.booleanConversion_result
      exact ⟨result, .choiceScalar type evaluated body⟩
    | true =>
      obtain ⟨result, body⟩ := yesIH values typed
      exact ⟨result, .choice type evaluated body⟩
  | choiceScalars type condition first second =>
    obtain ⟨encoded, evaluated⟩ := condition.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨encoded, body⟩ := second.evaluates values typed
      obtain ⟨result, rfl⟩ := body.booleanConversion_result
      exact ⟨result, .choiceScalar type evaluated body⟩
    | true =>
      obtain ⟨encoded, body⟩ := first.evaluates values typed
      obtain ⟨result, rfl⟩ := body.booleanConversion_result
      exact ⟨result, .choiceScalar type evaluated body⟩
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
  | letFlagResult _ body ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    obtain ⟨encoded, continuation⟩ := body.evaluates (.boolean flag :: values) (by simp [Value.kind, typed])
    obtain ⟨result, rfl⟩ := continuation.booleanConversion_result
    exact ⟨result, .letFlagResult evaluated continuation⟩
  | bindFlagResult input output _ body ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    obtain ⟨encoded, continuation⟩ := body.evaluates (.boolean flag :: values) (by simp [Value.kind, typed])
    obtain ⟨result, rfl⟩ := continuation.booleanConversion_result
    exact ⟨result, .bindFlagResult input output evaluated continuation⟩
  | letFlagBefore value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, body⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letFlagBefore evaluated body⟩
  | bindFlagBefore input output value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, body⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindFlagBefore input output evaluated body⟩
  | letBefore value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨flag, evaluated⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨flag, .letBefore hx evaluated⟩
  | bindBefore input output value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨flag, evaluated⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨flag, .bindBefore input output hx evaluated⟩
  | letResult value body =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨result, hr⟩ := body.evaluates (.word x :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := hr.booleanConversion_result
    exact ⟨flag, .letResult hx hr⟩
  | bindResult input output value body =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨result, hr⟩ := body.evaluates (.word x :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := hr.booleanConversion_result
    exact ⟨flag, .bindResult input output hx hr⟩
  | idFunctionInput input result _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .idFunctionInput input result evaluated⟩
  | idLet type _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .idLet type evaluated⟩
  | wrapped wrapper _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .wrapped wrapper evaluated⟩

end LeanExe.Source.Scalar.BooleanRange
