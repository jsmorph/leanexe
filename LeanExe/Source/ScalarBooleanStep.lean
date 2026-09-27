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

def scalarFunctionExpr (input output : Lean.Expr)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (value body : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE name (.forallE typeName input output typeBi)
    (.lam paramName input value paramBi) body nondep

/-- Nondependent inspection checks the complete result and binds its Boolean payload. -/
def casesExpr (output : BooleanType) (motiveName doneName yieldName : Lean.Name)
    (motiveBi doneBi yieldBi : Lean.BinderInfo) (value doneBody yieldBody : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ForInStep.casesOn [.succ .zero, .zero]) (.const ``Bool []))
    (.lam motiveName (resultType .boolean) (resultType output) motiveBi)) value)
    (.lam doneName (.const ``Bool []) doneBody doneBi))
    (.lam yieldName (.const ``Bool []) yieldBody yieldBi)

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

  | resultVar (present : values[index]? = some (.result outcome)) :
      Eval (.bvar index) values outcome
  | letResult (type : BooleanType) (value : Eval a values bound)
      (body : Eval b (.result bound :: values) outcome) :
      Eval (.letE name (resultType type) a b nondep) values outcome
  | bindResult (input output : BooleanType) (value : Eval a values bound)
      (body : Eval b (.result bound :: values) outcome) :
      Eval (bindExpr (resultType input) output name bi a b) values outcome

  | letResultFunction (input output : BooleanType)
      (function : ∀ result, Eval a (.result result :: values) (f result))
      (body : Eval b (.resultFunction f :: values) outcome) :
      Eval (functionExpr (resultType input) output name typeName paramName typeBi paramBi a b nondep) values outcome
  | resultApply (function : values[index]? = some (.resultFunction f))
      (argument : Eval a values bound) :
      Eval (.app (.bvar index) a) values (f bound)

  | letBinaryPredicate (helper : BooleanBinaryHelper)
      (function : ∀ x y, EvalWith (.app (.const ``Bool.toUInt64 []) helper.body)
        (.word y :: .word x :: values.map Value.toScalar) (Bool.toUInt64 (f x y)))
      (body : Eval helper.continuation (.scalar (.binaryPredicateFunction f) :: values) outcome) :
      Eval helper.expr values outcome
  | letScalarWordFunction (input : ResultType) (output : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values.map Value.toScalar) (f x))
      (body : Eval b (.scalar (.function false f) :: values) outcome) :
      Eval (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep) values outcome
  | letScalarPredicateFunction (input : ResultType) (output : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) a) (.word x :: values.map Value.toScalar) (Bool.toUInt64 (f x)))
      (body : Eval b (.scalar (.predicateFunction f) :: values) outcome) :
      Eval (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep) values outcome
  | letScalarBooleanFunction (input : BooleanType) (output : ResultType)
      (function : ∀ x, EvalWith a (.boolean x :: values.map Value.toScalar) (f x))
      (body : Eval b (.scalar (.booleanFunction f) :: values) outcome) :
      Eval (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep) values outcome
  | letScalarBooleanPredicateFunction (input : BooleanType) (output : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) a) (.boolean x :: values.map Value.toScalar) (Bool.toUInt64 (f x)))
      (body : Eval b (.scalar (.booleanPredicateFunction f) :: values) outcome) :
      Eval (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep) values outcome

  | casesDone (output : BooleanType) (value : Eval a values (.done flag))
      (body : Eval doneBody (.scalar (.boolean flag) :: values) outcome) :
      Eval (casesExpr output motiveName doneName yieldName motiveBi doneBi yieldBi a doneBody yieldBody) values outcome
  | casesYield (output : BooleanType) (value : Eval a values (.yield flag))
      (body : Eval yieldBody (.scalar (.boolean flag) :: values) outcome) :
      Eval (casesExpr output motiveName doneName yieldName motiveBi doneBi yieldBi a doneBody yieldBody) values outcome

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

  | resultVar (present : types[index]? = some .result) : Supported types (.bvar index)
  | letResult (type : BooleanType) (value : Supported types a)
      (body : Supported (.result :: types) b) :
      Supported types (.letE name (resultType type) a b nondep)
  | bindResult (input output : BooleanType) (value : Supported types a)
      (body : Supported (.result :: types) b) :
      Supported types (bindExpr (resultType input) output name bi a b)

  | letResultFunction (input output : BooleanType)
      (function : Supported (.result :: types) a)
      (body : Supported (.resultFunction :: types) b) :
      Supported types (functionExpr (resultType input) output name typeName paramName typeBi paramBi a b nondep)
  | resultApply (function : types[index]? = some .resultFunction) (argument : Supported types a) :
      Supported types (.app (.bvar index) a)

  | letBinaryPredicate (helper : BooleanBinaryHelper)
      (function : SupportedWith (.word :: .word :: types.map BindingKind.toScalar)
        (.app (.const ``Bool.toUInt64 []) helper.body))
      (body : Supported (.scalar .binaryPredicateFunction :: types) helper.continuation) :
      Supported types helper.expr
  | letScalarWordFunction (input : ResultType) (output : ResultType)
      (function : SupportedWith (.word :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar (.function false) :: types) b) :
      Supported types (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep)
  | letScalarPredicateFunction (input : ResultType) (output : BooleanType)
      (function : SupportedWith (.word :: types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.scalar (.predicateFunction) :: types) b) :
      Supported types (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep)
  | letScalarBooleanFunction (input : BooleanType) (output : ResultType)
      (function : SupportedWith (.boolean :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar (.booleanFunction) :: types) b) :
      Supported types (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep)
  | letScalarBooleanPredicateFunction (input : BooleanType) (output : BooleanType)
      (function : SupportedWith (.boolean :: types.map BindingKind.toScalar) (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.scalar (.booleanPredicateFunction) :: types) b) :
      Supported types (scalarFunctionExpr input.expr output.expr name typeName paramName typeBi paramBi a b nondep)

  | casesResult (output : BooleanType) (value : Supported types a)
      (doneBody : Supported (.scalar .boolean :: types) doneExpr)
      (yieldBody : Supported (.scalar .boolean :: types) yieldExpr) :
      Supported types (casesExpr output motiveName doneName yieldName motiveBi doneBi yieldBi a doneExpr yieldExpr)

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
  | resultVar present =>
    obtain ⟨outcome, found⟩ := result_lookup typed present
    exact ⟨outcome, .resultVar found⟩
  | letResult type _ _ ihv ihb =>
    obtain ⟨bound, hv⟩ := ihv values typed
    obtain ⟨outcome, hb⟩ := ihb (.result bound :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letResult type hv hb⟩
  | bindResult input output _ _ ihv ihb =>
    obtain ⟨bound, hv⟩ := ihv values typed
    obtain ⟨outcome, hb⟩ := ihb (.result bound :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .bindResult input output hv hb⟩
  | letResultFunction input output _ _ ihf ihb =>
    have total := fun result => ihf (.result result :: values) (by simp [Value.kind, typed])
    let f := fun result => (total result).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.resultFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letResultFunction input output (fun result => (total result).choose_spec) evaluated⟩
  | resultApply present _ ih =>
    obtain ⟨f, found⟩ := resultFunction_lookup typed present
    obtain ⟨bound, evaluated⟩ := ih values typed
    exact ⟨f bound, .resultApply found evaluated⟩
  | letBinaryPredicate helper function _ ih =>
    have total : ∀ x y, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) helper.body)
          (.word y :: .word x :: values.map Value.toScalar) flag.toUInt64 := by
      intro x y
      obtain ⟨encoded, evaluated⟩ := function.evaluates
        (.word y :: .word x :: values.map Value.toScalar)
        (by simpa [Scalar.Value.kind] using typed_projection typed)
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x y => (total x y).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.binaryPredicateFunction f) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letBinaryPredicate helper (fun x y => (total x y).choose_spec) evaluated⟩
  | @letScalarWordFunction types a b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have total (x : UInt64) := function.evaluates (.word x :: values.map Value.toScalar)
      (by simp [Scalar.Value.kind, typed_projection typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.function false f) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letScalarWordFunction input output (fun x => (total x).choose_spec) evaluated⟩
  | @letScalarPredicateFunction a types b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have total : ∀ x : UInt64, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) a) (.word x :: values.map Value.toScalar) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := function.evaluates (.word x :: values.map Value.toScalar)
        (by simp [Scalar.Value.kind, typed_projection typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.predicateFunction f) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letScalarPredicateFunction input output (fun x => (total x).choose_spec) evaluated⟩
  | @letScalarBooleanFunction types a b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have total (x : Bool) := function.evaluates (.boolean x :: values.map Value.toScalar)
      (by simp [Scalar.Value.kind, typed_projection typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.booleanFunction f) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letScalarBooleanFunction input output (fun x => (total x).choose_spec) evaluated⟩
  | @letScalarBooleanPredicateFunction a types b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have total : ∀ x : Bool, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) a) (.boolean x :: values.map Value.toScalar) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := function.evaluates (.boolean x :: values.map Value.toScalar)
        (by simp [Scalar.Value.kind, typed_projection typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.booleanPredicateFunction f) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letScalarBooleanPredicateFunction input output (fun x => (total x).choose_spec) evaluated⟩
  | casesResult output value doneBody yieldBody ihv ihd ihy =>
    obtain ⟨result, evaluated⟩ := ihv values typed
    cases result with
    | done flag =>
      obtain ⟨outcome, body⟩ := ihd (.scalar (.boolean flag) :: values)
        (by simp [Value.kind, Scalar.Value.kind, typed])
      exact ⟨outcome, .casesDone output evaluated body⟩
    | yield flag =>
      obtain ⟨outcome, body⟩ := ihy (.scalar (.boolean flag) :: values)
        (by simp [Value.kind, Scalar.Value.kind, typed])
      exact ⟨outcome, .casesYield output evaluated body⟩

end LeanExe.Source.Scalar.BooleanStep
