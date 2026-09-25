import LeanExe.Source.ScalarManyFunctionSemantics
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
  | yieldDirect (value : EvalWith a (values.map Value.toScalar) x) :
      Eval (yieldDirect a) values (.yield x)
  | doneDirect (value : EvalWith a (values.map Value.toScalar) x) :
      Eval (doneDirect a) values (.done x)
  | choose (op : Comparison) (type : ResultAnnotation)
      (left : EvalWith a (values.map Value.toScalar) x) (right : EvalWith b (values.map Value.toScalar) y)
      (chosen : Eval (if op.denote x y then onTrue else onFalse) values outcome) :
      Eval (branch op type a b onTrue onFalse) values outcome
  | chooseCompound (guard : CompoundGuard) (type : ResultAnnotation) {native : Lean.Expr → UInt64}
      (arguments : ∀ expression, expression ∈ guard.operands →
        EvalWith expression (values.map Value.toScalar) (native expression))
      (chosen : Eval (if guard.denote native then onTrue else onFalse) values outcome) :
      Eval (guard.branch (resultType type) onTrue onFalse) values outcome
  | chooseDependent (guard : Guard) (type : ResultAnnotation)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo) {native : Lean.Expr → UInt64}
      (arguments : ∀ expression, expression ∈ guard.operands →
        EvalWith expression (values.map Value.toScalar) (native expression))
      (branch : Eval (if guard.denote native then onTrue else onFalse) (.scalar .unit :: values) outcome) :
      Eval (guard.dependentBranch (resultType type) trueName falseName trueBi falseBi onTrue onFalse) values outcome
  | letBoolean (expression : BooleanLocal) {native : Lean.Expr → UInt64} {booleans : Nat → Bool}
      (variables : expression.VariablesMean (values.map Value.toScalar) booleans)
      (arguments : ∀ operand, operand ∈ expression.operands → EvalWith operand (values.map Value.toScalar) (native operand))
      (body : Eval b (.scalar (.boolean (expression.denote native booleans)) :: values) value) :
      Eval (.letE name (.const ``Bool []) expression.expr b nondep) values value
  | idBindBoolean (action : BooleanAction) (type : ResultAnnotation) {native : Lean.Expr → UInt64} {booleans : Nat → Bool}
      (variables : action.leaf.VariablesMean (values.map Value.toScalar) booleans)
      (arguments : ∀ operand, operand ∈ action.leaf.operands → EvalWith operand (values.map Value.toScalar) (native operand))
      (body : Eval b (.scalar (.boolean (action.leaf.denote native booleans)) :: values) value) :
      Eval (BooleanIdentity.bind name bi action.expr b (resultType type)) values value
  | chooseBoolean (guard : BooleanLocalGuard) (type : ResultAnnotation)
      {native : Lean.Expr → UInt64} {booleans : Nat → Bool}
      (variables : guard.value.VariablesMean (values.map Value.toScalar) booleans)
      (arguments : ∀ operand, operand ∈ guard.value.operands → EvalWith operand (values.map Value.toScalar) (native operand))
      (branch : Eval (if guard.value.denote native booleans then t else e) values value) :
      Eval (guard.branch (resultType type) t e) values value
  | chooseBooleanDependent (guard : BooleanLocalGuard) (type : ResultAnnotation)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      {native : Lean.Expr → UInt64} {booleans : Nat → Bool}
      (variables : guard.value.VariablesMean (values.map Value.toScalar) booleans)
      (arguments : ∀ operand, operand ∈ guard.value.operands → EvalWith operand (values.map Value.toScalar) (native operand))
      (branch : Eval (if guard.value.denote native booleans then t else e) (.scalar .unit :: values) value) :
      Eval (guard.dependentBranch (resultType type) trueName falseName trueBi falseBi t e) values value
  | letE (value : EvalWith a (values.map Value.toScalar) x)
      (body : Eval b (.scalar (.word x) :: values) outcome) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values outcome
  | idBind (type : ResultAnnotation) (value : EvalWith a (values.map Value.toScalar) x)
      (body : Eval b (.scalar (.word x) :: values) outcome) :
      Eval (bindWord name bi type a b) values outcome
  | letBinaryFn (type : ResultType)
      (function : ∀ x y, EvalWith a (.word y :: .word x :: values.map Value.toScalar) (f x y))
      (body : Eval b (.scalar (.binaryFunction f) :: values) outcome) :
      Eval (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) values outcome
  | letManyFn (shape : ManyFunction)
      (function : ∀ arguments : List UInt64, arguments.length = shape.arity →
        EvalWith shape.body (arguments.reverse.map Scalar.Value.word ++ values.map Value.toScalar) (f arguments))
      (body : Eval b (.scalar (.manyFunction shape.arity f) :: values) outcome) :
      Eval (shape.bind name b nondep) values outcome
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values.map Value.toScalar) (f x))
      (body : Eval b (.scalar (.function false f) :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values.map Value.toScalar) (f x))
      (body : Eval b (.scalar (.function true f) :: values) outcome) :
      Eval (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values outcome
  | manyApply (call : ManyCall) {native : Lean.Expr → UInt64}
      (function : values[call.index]? = some (.manyFunction call.arity f))
      (arguments : ∀ operand, operand ∈ call.arguments →
        EvalWith operand (values.map Value.toScalar) (native operand)) :
      Eval call.expr values (f (call.arguments.map native))
  | letManyStepFn (shape : ManyFunction)
      (function : ∀ arguments : List UInt64, arguments.length = shape.arity →
        Eval shape.body (arguments.reverse.map (fun value => .scalar (.word value)) ++ values) (f arguments))
      (body : Eval b (.manyFunction shape.arity f :: values) outcome) :
      Eval (shape.bind name b nondep resultType) values outcome
  | binaryApply (function : values[index]? = some (.binaryFunction f))
      (first : EvalWith a (values.map Value.toScalar) x)
      (second : EvalWith b (values.map Value.toScalar) y) :
      Eval (.app (.app (.bvar index) a) b) values (f x y)
  | letBinaryStepFn (type : ResultAnnotation)
      (function : ∀ x y, Eval a (.scalar (.word y) :: .scalar (.word x) :: values) (f x y))
      (body : Eval b (.binaryFunction f :: values) outcome) :
      Eval (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) (resultType type) secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) values outcome
  | apply (function : values[index]? = some (.function false f))
      (argument : EvalWith a (values.map Value.toScalar) x) :
      Eval (.app (.bvar index) a) values (f x)
  | unitApply (unitForm : UnitSyntax) (function : values[index]? = some (.function true f))
      (argument : EvalWith a (values.map Value.toScalar) x) :
      Eval (.app (.app (.bvar index) unitForm.value) a) values (f x)
  | letStepFn (type : ResultAnnotation)
      (function : ∀ x, Eval a (.scalar (.word x) :: values) (f x))
      (body : Eval b (.function false f :: values) outcome) :
      Eval (.letE name
        (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values outcome
  | letUnitStepFn (type : ResultAnnotation) (unitForm : UnitSyntax)
      (function : ∀ x, Eval a (.scalar (.word x) :: .scalar .unit :: values) (f x))
      (body : Eval b (.function true f :: values) outcome) :
      Eval (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values outcome
  | applyResult (function : values[index]? = some (.resultFunction f))
      (argument : Eval a values input) : Eval (.app (.bvar index) a) values (f input)
  | letResultFn (input output : ResultAnnotation)
      (function : ∀ outcome, Eval a (.result outcome :: values) (f outcome))
      (body : Eval b (.resultFunction f :: values) outcome) :
      Eval (.letE name (.forallE typeName (resultType input) (resultType output) typeBi)
        (.lam paramName (resultType input) a paramBi) b nondep) values outcome
  | resultVar (present : values[index]? = some (.result outcome)) :
      Eval (.bvar index) values outcome
  | idRun (type : ResultAnnotation) (body : Eval a values outcome) : Eval (idRun type a) values outcome
  | idPure (type : ResultAnnotation) (body : Eval a values outcome) : Eval (idPure type a) values outcome
  | letResult (type : ResultAnnotation) (value : Eval a values bound)
      (body : Eval b (.result bound :: values) outcome) :
      Eval (.letE name (resultType type) a b nondep) values outcome
  | bindResult (input output : ResultAnnotation) (value : Eval a values bound)
      (body : Eval b (.result bound :: values) outcome) :
      Eval (bindResult name bi input output a b) values outcome
  | metadata (body : Eval a values outcome) : Eval (.mdata data a) values outcome

/-- Independent source support for a body returning ForInStep UInt64.
Every scalar subterm uses the ordinary scalar grammar; step functions are
available only through step calls, never as scalar-valued functions. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | yieldValue (value : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (Range.yieldValue a)
  | doneValue (value : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (doneValue a)
  | yieldDirect (value : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (yieldDirect a)
  | doneDirect (value : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (doneDirect a)
  | choose (op : Comparison) (type : ResultAnnotation)
      (left : SupportedWith (types.map BindingKind.toScalar) a)
      (right : SupportedWith (types.map BindingKind.toScalar) b)
      (onTrue : Supported types t) (onFalse : Supported types e) :
      Supported types (branch op type a b t e)
  | chooseCompound (guard : CompoundGuard) (type : ResultAnnotation)
      (arguments : ∀ expression, expression ∈ guard.operands →
        SupportedWith (types.map BindingKind.toScalar) expression)
      (onTrue : Supported types t) (onFalse : Supported types e) :
      Supported types (guard.branch (resultType type) t e)
  | chooseDependent (guard : Guard) (type : ResultAnnotation)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      (arguments : ∀ expression, expression ∈ guard.operands →
        SupportedWith (types.map BindingKind.toScalar) expression)
      (onTrue : Supported (.scalar .unit :: types) t) (onFalse : Supported (.scalar .unit :: types) e) :
      Supported types (guard.dependentBranch (resultType type) trueName falseName trueBi falseBi t e)
  | letBoolean (expression : BooleanLocal)
      (variables : expression.VariablesTyped (types.map BindingKind.toScalar))
      (arguments : ∀ operand, operand ∈ expression.operands → SupportedWith (types.map BindingKind.toScalar) operand)
      (body : Supported (.scalar .boolean :: types) b) :
      Supported types (.letE name (.const ``Bool []) expression.expr b nondep)
  | idBindBoolean (action : BooleanAction) (type : ResultAnnotation)
      (variables : action.leaf.VariablesTyped (types.map BindingKind.toScalar))
      (arguments : ∀ operand, operand ∈ action.leaf.operands → SupportedWith (types.map BindingKind.toScalar) operand)
      (body : Supported (.scalar .boolean :: types) b) :
      Supported types (BooleanIdentity.bind name bi action.expr b (resultType type))
  | chooseBoolean (guard : BooleanLocalGuard) (type : ResultAnnotation)
      (variables : guard.value.VariablesTyped (types.map BindingKind.toScalar))
      (arguments : ∀ operand, operand ∈ guard.value.operands → SupportedWith (types.map BindingKind.toScalar) operand)
      (onTrue : Supported types t) (onFalse : Supported types e) :
      Supported types (guard.branch (resultType type) t e)
  | chooseBooleanDependent (guard : BooleanLocalGuard) (type : ResultAnnotation)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      (variables : guard.value.VariablesTyped (types.map BindingKind.toScalar))
      (arguments : ∀ operand, operand ∈ guard.value.operands → SupportedWith (types.map BindingKind.toScalar) operand)
      (onTrue : Supported (.scalar .unit :: types) t) (onFalse : Supported (.scalar .unit :: types) e) :
      Supported types (guard.dependentBranch (resultType type) trueName falseName trueBi falseBi t e)
  | letE (value : SupportedWith (types.map BindingKind.toScalar) a)
      (body : Supported (.scalar .word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | idBind (type : ResultAnnotation) (value : SupportedWith (types.map BindingKind.toScalar) a)
      (body : Supported (.scalar .word :: types) b) :
      Supported types (bindWord name bi type a b)
  | letBinaryFn (type : ResultType)
      (function : SupportedWith (.word :: .word :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar .binaryFunction :: types) b) :
      Supported types (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)
  | letManyFn (shape : ManyFunction)
      (function : SupportedWith (List.replicate shape.arity .word ++ types.map BindingKind.toScalar) shape.body)
      (body : Supported (.scalar (.manyFunction shape.arity) :: types) b) :
      Supported types (shape.bind name b nondep)
  | letFn (type : ResultType)
      (function : SupportedWith (.word :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar (.function false) :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax)
      (function : SupportedWith (.word :: .unit :: types.map BindingKind.toScalar) a)
      (body : Supported (.scalar (.function true) :: types) b) :
      Supported types (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | manyApply (call : ManyCall)
      (function : types[call.index]? = some (.manyFunction call.arity))
      (arguments : ∀ operand, operand ∈ call.arguments →
        SupportedWith (types.map BindingKind.toScalar) operand) :
      Supported types call.expr
  | letManyStepFn (shape : ManyFunction)
      (function : Supported (List.replicate shape.arity (.scalar .word) ++ types) shape.body)
      (body : Supported (.manyFunction shape.arity :: types) b) :
      Supported types (shape.bind name b nondep resultType)
  | binaryApply (function : types[index]? = some .binaryFunction)
      (first : SupportedWith (types.map BindingKind.toScalar) a)
      (second : SupportedWith (types.map BindingKind.toScalar) b) :
      Supported types (.app (.app (.bvar index) a) b)
  | letBinaryStepFn (type : ResultAnnotation)
      (function : Supported (.scalar .word :: .scalar .word :: types) a)
      (body : Supported (.binaryFunction :: types) b) :
      Supported types (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) (resultType type) secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)
  | apply (function : types[index]? = some (.function false))
      (argument : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (.app (.bvar index) a)
  | unitApply (unitForm : UnitSyntax) (function : types[index]? = some (.function true))
      (argument : SupportedWith (types.map BindingKind.toScalar) a) :
      Supported types (.app (.app (.bvar index) unitForm.value) a)
  | letStepFn (type : ResultAnnotation) (function : Supported (.scalar .word :: types) a)
      (body : Supported (.function false :: types) b) :
      Supported types (.letE name
        (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letUnitStepFn (type : ResultAnnotation) (unitForm : UnitSyntax)
      (function : Supported (.scalar .word :: .scalar .unit :: types) a)
      (body : Supported (.function true :: types) b) :
      Supported types (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) (resultType type) typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | applyResult (function : types[index]? = some .resultFunction)
      (argument : Supported types a) : Supported types (.app (.bvar index) a)
  | letResultFn (input output : ResultAnnotation)
      (function : Supported (.result :: types) a)
      (body : Supported (.resultFunction :: types) b) :
      Supported types (.letE name (.forallE typeName (resultType input) (resultType output) typeBi)
        (.lam paramName (resultType input) a paramBi) b nondep)
  | resultVar (present : types[index]? = some .result) : Supported types (.bvar index)
  | idRun (type : ResultAnnotation) (body : Supported types a) : Supported types (idRun type a)
  | idPure (type : ResultAnnotation) (body : Supported types a) : Supported types (idPure type a)
  | letResult (type : ResultAnnotation) (value : Supported types a)
      (body : Supported (.result :: types) b) :
      Supported types (.letE name (resultType type) a b nondep)
  | bindResult (input output : ResultAnnotation) (value : Supported types a) (body : Supported (.result :: types) b) :
      Supported types (bindResult name bi input output a b)
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
  | yieldDirect value =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨.yield x, .yieldDirect hx⟩
  | doneDirect value =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨.done x, .doneDirect hx⟩
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
  | chooseCompound guard type arguments _ _ it ie =>
    have total := fun expression member =>
      (arguments expression member).evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun expression =>
      if member : expression ∈ guard.operands then (total expression member).choose else 0
    have meanings : ∀ expression, expression ∈ guard.operands →
        EvalWith expression (values.map Value.toScalar) (native expression) := by
      intro expression member
      simpa [native, member] using (total expression member).choose_spec
    cases flag : guard.denote native with
    | false =>
      obtain ⟨outcome, evaluated⟩ := ie values typed
      exact ⟨outcome, .chooseCompound guard type meanings (by simpa [flag] using evaluated)⟩
    | true =>
      obtain ⟨outcome, evaluated⟩ := it values typed
      exact ⟨outcome, .chooseCompound guard type meanings (by simpa [flag] using evaluated)⟩
  | chooseDependent guard type tn fn tb fb arguments _ _ it ie =>
    have total := fun expression member =>
      (arguments expression member).evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun expression =>
      if member : expression ∈ guard.operands then (total expression member).choose else 0
    have meanings : ∀ expression, expression ∈ guard.operands →
        EvalWith expression (values.map Value.toScalar) (native expression) := by
      intro expression member
      simpa only [native, dite_eq_left member] using (total expression member).choose_spec
    cases flag : guard.denote native with
    | false =>
      obtain ⟨outcome, evaluated⟩ := ie (.scalar .unit :: values)
        (by simp [Value.kind, Scalar.Value.kind, typed])
      exact ⟨outcome, .chooseDependent guard type tn fn tb fb meanings (by simpa [flag] using evaluated)⟩
    | true =>
      obtain ⟨outcome, evaluated⟩ := it (.scalar .unit :: values)
        (by simp [Value.kind, Scalar.Value.kind, typed])
      exact ⟨outcome, .chooseDependent guard type tn fn tb fb meanings (by simpa [flag] using evaluated)⟩
  | letBoolean expression variables arguments _ ihb =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ expression.operands then ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose else 0
    have meanings : ∀ operand, operand ∈ expression.operands → EvalWith operand (values.map Value.toScalar) (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose_spec
    obtain ⟨result, body⟩ := ihb (.scalar (.boolean (expression.denote native booleans)) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨result, .letBoolean expression hbooleans meanings body⟩
  | idBindBoolean action type variables arguments _ ihb =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ action.leaf.operands then ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose else 0
    have meanings : ∀ operand, operand ∈ action.leaf.operands → EvalWith operand (values.map Value.toScalar) (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose_spec
    obtain ⟨result, body⟩ := ihb (.scalar (.boolean (action.leaf.denote native booleans)) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨result, .idBindBoolean action type hbooleans meanings body⟩
  | chooseBoolean guard type variables arguments _ _ iht ihe =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ guard.value.operands then ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose else 0
    have meanings : ∀ operand, operand ∈ guard.value.operands → EvalWith operand (values.map Value.toScalar) (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose_spec
    cases flag : guard.value.denote native booleans with
    | false =>
      obtain ⟨value, body⟩ := ihe values typed
      exact ⟨value, .chooseBoolean guard type hbooleans meanings (by simpa [flag] using body)⟩
    | true =>
      obtain ⟨value, body⟩ := iht values typed
      exact ⟨value, .chooseBoolean guard type hbooleans meanings (by simpa [flag] using body)⟩
  | chooseBooleanDependent guard type tn fn tb fb variables arguments _ _ iht ihe =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ guard.value.operands then ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose else 0
    have meanings : ∀ operand, operand ∈ guard.value.operands → EvalWith operand (values.map Value.toScalar) (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using ((arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)).choose_spec
    cases flag : guard.value.denote native booleans with
    | false =>
      obtain ⟨value, body⟩ := ihe (.scalar .unit :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
      exact ⟨value, .chooseBooleanDependent guard type tn fn tb fb hbooleans meanings (by simpa [flag] using body)⟩
    | true =>
      obtain ⟨value, body⟩ := iht (.scalar .unit :: values) (by simp [Value.kind, Scalar.Value.kind, typed])
      exact ⟨value, .chooseBooleanDependent guard type tn fn tb fb hbooleans meanings (by simpa [flag] using body)⟩
  | letE value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.word x) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letE hx evaluated⟩
  | idBind type value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.word x) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .idBind type hx evaluated⟩
  | letBinaryFn type function _ ih =>
    have total := fun x y => function.evaluates (.word y :: .word x :: values.map Value.toScalar)
      (by simpa [LeanExe.Source.Scalar.Value.kind] using typed_projection typed)
    let f := fun x y => (total x y).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.binaryFunction f) :: values)
      (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letBinaryFn type (fun x y => (total x y).choose_spec) evaluated⟩
  | letManyFn shape function _ ih =>
    obtain ⟨f, meanings⟩ := function.manyFunction_evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.manyFunction shape.arity f) :: values)
      (by simp [Value.kind, Scalar.Value.kind, typed])
    exact ⟨outcome, .letManyFn shape meanings evaluated⟩
  | letFn type function _ ih =>
    have total := fun x => function.evaluates (.word x :: values.map Value.toScalar)
      (by simpa [LeanExe.Source.Scalar.Value.kind] using typed_projection typed)
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.function false f) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letFn type (fun x => (total x).choose_spec) evaluated⟩
  | letUnitFn type unitForm function _ ih =>
    have total := fun x => function.evaluates (.word x :: .unit :: values.map Value.toScalar)
      (by simpa [LeanExe.Source.Scalar.Value.kind] using typed_projection typed)
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ih (.scalar (.function true f) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    exact ⟨outcome, .letUnitFn type unitForm (fun x => (total x).choose_spec) evaluated⟩
  | manyApply call present arguments =>
    obtain ⟨f, hf⟩ := manyFunction_lookup typed present
    have total := fun operand member =>
      (arguments operand member).evaluates (values.map Value.toScalar) (typed_projection typed)
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ call.arguments then (total operand member).choose else 0
    have meanings : ∀ operand, operand ∈ call.arguments →
        EvalWith operand (values.map Value.toScalar) (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (total operand member).choose_spec
    exact ⟨f (call.arguments.map native), .manyApply call hf meanings⟩
  | letManyStepFn shape _ _ ihf ihb =>
    have total := fun (arguments : List UInt64) (len : arguments.length = shape.arity) =>
      ihf (arguments.reverse.map (fun value => .scalar (.word value)) ++ values)
        (by simp [List.map_map, Function.comp_def, Value.kind, Scalar.Value.kind, List.map_const', len, typed])
    let f : List UInt64 → ForInStep UInt64 := fun arguments =>
      if len : arguments.length = shape.arity then (total arguments len).choose else .yield 0
    have meanings : ∀ arguments : List UInt64, arguments.length = shape.arity →
        Eval shape.body (arguments.reverse.map (fun value => .scalar (.word value)) ++ values) (f arguments) := by
      intro arguments len
      simpa only [f, dite_eq_left len] using (total arguments len).choose_spec
    obtain ⟨outcome, evaluated⟩ := ihb (.manyFunction shape.arity f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letManyStepFn shape meanings evaluated⟩
  | binaryApply present first second =>
    obtain ⟨f, hf⟩ := binaryFunction_lookup typed present
    obtain ⟨x, hx⟩ := first.evaluates (values.map Value.toScalar) (typed_projection typed)
    obtain ⟨y, hy⟩ := second.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨f x y, .binaryApply hf hx hy⟩
  | letBinaryStepFn type _ _ ihf ihb =>
    have total := fun x y => ihf (.scalar (.word y) :: .scalar (.word x) :: values)
      (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    let f := fun x y => (total x y).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.binaryFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letBinaryStepFn type (fun x y => (total x y).choose_spec) evaluated⟩
  | apply present argument =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := argument.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨f x, .apply hf hx⟩
  | unitApply unitForm present argument =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := argument.evaluates (values.map Value.toScalar) (typed_projection typed)
    exact ⟨f x, .unitApply unitForm hf hx⟩
  | letStepFn type _ _ ihf ihb =>
    have total := fun x => ihf (.scalar (.word x) :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letStepFn type (fun x => (total x).choose_spec) evaluated⟩
  | letUnitStepFn type unitForm _ _ ihf ihb =>
    have total := fun x => ihf (.scalar (.word x) :: .scalar .unit :: values) (by simp [Value.kind, LeanExe.Source.Scalar.Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.function true f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letUnitStepFn type unitForm (fun x => (total x).choose_spec) evaluated⟩
  | applyResult present _ ih =>
    obtain ⟨f, hf⟩ := resultFunction_lookup typed present
    obtain ⟨input, evaluated⟩ := ih values typed
    exact ⟨f input, .applyResult hf evaluated⟩
  | letResultFn input output _ _ ihf ihb =>
    have total := fun result => ihf (.result result :: values) (by simp [Value.kind, typed])
    let f := fun result => (total result).choose
    obtain ⟨outcome, evaluated⟩ := ihb (.resultFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letResultFn input output (fun result => (total result).choose_spec) evaluated⟩
  | resultVar present =>
    obtain ⟨outcome, found⟩ := result_lookup typed present
    exact ⟨outcome, .resultVar found⟩
  | idRun type _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .idRun type evaluated⟩
  | idPure type _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .idPure type evaluated⟩
  | letResult type _ _ ihv ihb =>
    obtain ⟨bound, hv⟩ := ihv values typed
    obtain ⟨outcome, hb⟩ := ihb (.result bound :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .letResult type hv hb⟩
  | bindResult input output _ _ ihv ihb =>
    obtain ⟨bound, hv⟩ := ihv values typed
    obtain ⟨outcome, hb⟩ := ihb (.result bound :: values) (by simp [Value.kind, typed])
    exact ⟨outcome, .bindResult input output hv hb⟩
  | metadata _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .metadata evaluated⟩

end LeanExe.Source.Scalar.Step
