import LeanExe.Source.ScalarStep
import LeanExe.Source.ScalarRangeExitSyntax
import LeanExe.Source.ScalarRangeStride

namespace LeanExe.Source.Scalar.Range.Exit

/-- Native source evaluation of one range with yielding or done steps, with
pure scalar computations before and after it. -/
inductive Eval : Lean.Expr → List Scalar.Value → UInt64 → Prop where
  | range (indexType : IndexType) (stride : Stride) {stepFn : Nat → UInt64 → ForInStep UInt64}
      (first : Count.Eval firstExpr values begin) (count : Count.Eval countExpr values stop) (initial : EvalWith initialExpr values start)
      (step : ∀ index accumulator, Step.Eval body
        (.scalar (.word accumulator) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (stepFn index accumulator)) :
      Eval (call indexType stride firstExpr countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
        values (iterate (fun i accumulator => stepFn (begin + stride.number * i) accumulator)
          (trips (stop - begin) stride.number) 0 start)
  | letBoolean (bound : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) outcome) :
      Eval (.letE name (.const ``Bool []) a b nondep) values outcome
  | idBindBoolean (action : BooleanAction) (type : ResultType) (bound : EvalWith (.app (.const ``Bool.toUInt64 []) action.expr) values (Bool.toUInt64 flag))
      (body : Eval b (.boolean flag :: values) outcome) :
      Eval (BooleanIdentity.bind name bi action.expr b type.expr) values outcome
  | letE (value : EvalWith a values x) (body : Eval b (.word x :: values) y) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (type : ResultType) (body : Eval e values result) : Eval (Identity.run e type) values result
  | idPure (type : ResultType) (body : Eval e values result) : Eval (Identity.pure e type) values result
  | bindRight (input output : ResultType) (value : EvalWith a values x) (body : Eval b (.word x :: values) y) :
      Eval (Identity.bind name bi a b input output) values y
  | bindLeft (input output : ResultType) (value : Eval a values x) (body : EvalWith b (.word x :: values) y) :
      Eval (Identity.bind name bi a b input output) values y
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values) (f x))
      (body : Eval b (.function false f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
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
  | predicateInput (input : ResultType) (result : BooleanType)
      (inner : Eval (predicateInputExpr input result name typeName paramName typeBi paramBi a b nondep) values outcome) :
      Eval (predicateInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep) values outcome
  | booleanInput (input : BooleanType) (result : Lean.Expr)
      (inner : Eval (booleanInputExpr input result name typeName paramName typeBi paramBi a b nondep) values outcome) :
      Eval (booleanInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep) values outcome
  | letBooleanFn (type : ResultType)
      (function : ∀ x, EvalWith a (.boolean x :: values) (f x))
      (body : Eval b (.booleanFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) a paramBi) b nondep) values outcome
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
  | letLeft (value : Eval a values x) (body : EvalWith b (.word x :: values) y) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values y
  | idLet (body : Eval (.letE name type a b nondep) values result) :
      Eval (idLetExpr name type a b nondep) values result
  | metadata (body : Eval e values result) : Eval (.mdata data e) values result

/-- Independent source support for a single bounded early-exit range. -/
inductive Supported : List Scalar.BindingKind → Lean.Expr → Prop where
  | range (indexType : IndexType) (stride : Stride) (first : Count.Supported types firstExpr) (count : Count.Supported types countExpr) (initial : SupportedWith types initialExpr)
      (step : Step.Supported
        (.scalar .word :: .scalar .natural :: types.map Step.BindingKind.scalar) body) :
      Supported types
        (call indexType stride firstExpr countExpr initialExpr indexName accumulatorName indexBi accumulatorBi body)
  | letBoolean (bound : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) :
      Supported types (.letE name (.const ``Bool []) a b nondep)
  | idBindBoolean (action : BooleanAction) (type : ResultType) (bound : SupportedWith types (.app (.const ``Bool.toUInt64 []) action.expr))
      (body : Supported (.boolean :: types) b) :
      Supported types (BooleanIdentity.bind name bi action.expr b type.expr)
  | letE (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (type : ResultType) (body : Supported types e) : Supported types (Identity.run e type)
  | idPure (type : ResultType) (body : Supported types e) : Supported types (Identity.pure e type)
  | bindRight (input output : ResultType) (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (Identity.bind name bi a b input output)
  | bindLeft (input output : ResultType) (value : Supported types a) (body : SupportedWith (.word :: types) b) :
      Supported types (Identity.bind name bi a b input output)
  | letFn (type : ResultType) (function : SupportedWith (.word :: types) a)
      (body : Supported (.function false :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
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
  | predicateInput (input : ResultType) (result : BooleanType)
      (inner : Supported types (predicateInputExpr input result name typeName paramName typeBi paramBi a b nondep)) :
      Supported types (predicateInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep)
  | booleanInput (input : BooleanType) (result : Lean.Expr)
      (inner : Supported types (booleanInputExpr input result name typeName paramName typeBi paramBi a b nondep)) :
      Supported types (booleanInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep)
  | letBooleanFn (type : ResultType) (function : SupportedWith (.boolean :: types) a)
      (body : Supported (.booleanFunction :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) a paramBi) b nondep)
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
  | letLeft (value : Supported types a) (body : SupportedWith (.word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | idLet (body : Supported types (.letE name type a b nondep)) :
      Supported types (idLetExpr name type a b nondep)
  | metadata (body : Supported types e) : Supported types (.mdata data e)

theorem Supported.evaluates {types : List Scalar.BindingKind} {expr : Lean.Expr}
    (supported : Supported types expr) (values : List Scalar.Value)
    (typed : values.map Scalar.Value.kind = types) : ∃ value, Eval expr values value := by
  classical
  induction supported generalizing values with
  | range indexType stride first count initial step =>
    obtain ⟨begin, hbegin⟩ := first.evaluates values typed
    obtain ⟨stop, hstop⟩ := count.evaluates values typed
    obtain ⟨start, hstart⟩ := initial.evaluates values typed
    have total (index : Nat) (value : UInt64) :=
      step.evaluates (.scalar (.word value) :: .scalar (.natural index) :: values.map Step.Value.scalar)
        (by simp [Step.Value.kind, Scalar.Value.kind, List.map_map, Function.comp_def, ← typed])
    let f := fun index value => (total index value).choose
    exact ⟨iterate (fun i accumulator => f (begin + stride.number * i) accumulator)
      (trips (stop - begin) stride.number) 0 start, .range indexType stride hbegin hstop hstart
      (fun index value => (total index value).choose_spec)⟩
  | letBoolean bound _ ihb =>
    obtain ⟨encoded, hv⟩ := bound.evaluates values typed
    obtain ⟨flag, rfl⟩ := hv.booleanConversion_result
    obtain ⟨result, hb⟩ := ihb (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letBoolean hv hb⟩
  | idBindBoolean action type bound _ ihb =>
    obtain ⟨encoded, hv⟩ := bound.evaluates values typed
    obtain ⟨flag, rfl⟩ := hv.booleanConversion_result
    obtain ⟨result, hb⟩ := ihb (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .idBindBoolean action type hv hb⟩
  | letE value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨y, hy⟩ := ih (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .letE hx hy⟩
  | idRun type _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idRun type hv⟩
  | idPure type _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idPure type hv⟩
  | bindRight input output value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨y, hy⟩ := ih (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .bindRight input output hx hy⟩
  | bindLeft input output _ body ih =>
    obtain ⟨x, hx⟩ := ih values typed
    obtain ⟨y, hy⟩ := body.evaluates (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .bindLeft input output hx hy⟩
  | letFn type function _ ihb =>
    have total := fun x => function.evaluates (.word x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letFn type (fun x => (total x).choose_spec) hv⟩
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
  | predicateInput input result _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .predicateInput input result evaluated⟩
  | booleanInput input result _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .booleanInput input result evaluated⟩
  | letBooleanFn type function _ ihb =>
    have total := fun x => function.evaluates (.boolean x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.booleanFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBooleanFn type (fun x => (total x).choose_spec) hv⟩
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
  | letLeft _ body ih =>
    obtain ⟨x, hx⟩ := ih values typed
    obtain ⟨y, hy⟩ := body.evaluates (.word x :: values) (by simp [Scalar.Value.kind, typed])
    exact ⟨y, .letLeft hx hy⟩
  | idLet _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idLet hv⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

end LeanExe.Source.Scalar.Range.Exit
