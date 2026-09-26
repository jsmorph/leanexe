import LeanExe.Source.ScalarLetAnnotation
import LeanExe.Source.ScalarTypedLiteralInstance
import LeanExe.Source.ScalarBooleanAction
import LeanExe.Source.ScalarLiteralInstance
import LeanExe.Source.ScalarCall
import LeanExe.Source.ScalarUnit
import LeanExe.Source.ScalarHead
import LeanExe.Source.ScalarComplement
import LeanExe.Source.ScalarExtremum
import LeanExe.Source.ScalarBooleanLocalValues
import LeanExe.Source.ScalarValues
import LeanExe.Source.ScalarDependentBranch
import LeanExe.Source.ScalarCompoundGuard
import LeanExe.Source.ScalarRangeSyntax

namespace LeanExe.Source.Scalar

/-! Semantics of concrete, elaborated Lean UInt64 shape. The constants below
are paired explicitly with their native Lean definitions, independently of the
extractor's dispatch table and the IR operation selected by compilation.
The fragment covers pure arithmetic, UInt64 let bindings and comparison-based
conditionals and standard Id operations. Local scalar functions capture their lexical environment and accept finite UInt64 parameter lists. Iteration remains a separate obligation.
-/

def literalExpr (n : Nat) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n)))
    (.app (.const ``UInt64.instOfNat []) (.lit (.natVal n)))

inductive EvalWith : Lean.Expr → List Value → UInt64 → Prop where
  | var (h : values[index]? = some (.word value)) : EvalWith (.bvar index) values value
  | natural (h : values[index]? = some (.natural value)) :
      EvalWith (.app (.const ``UInt64.ofNat levels) (.bvar index)) values (UInt64.ofNat value)
  | literal : EvalWith (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
      values (UInt64.ofNat n)
  | ofNat : EvalWith (literalExpr n) values (UInt64.ofNat n)
  | ofNatInstance (instanceMeaning : LiteralInstance n 0 evidence) :
      EvalWith (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n))) evidence) values (UInt64.ofNat n)
  | naturalLiteral (numberMeaning : NaturalLiteral n numeral) :
      EvalWith (.app (.const ``UInt64.ofNat levels) numeral) values (UInt64.ofNat n)
  | ofNatNatural (numberMeaning : NaturalLiteral n numeral) (instanceMeaning : LiteralInstance n 0 evidence) :
      EvalWith (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) numeral) evidence) values (UInt64.ofNat n)
  | complement (head : ComplementHead operation) (argument : EvalWith a values x) :
      EvalWith (.app operation a) values (UInt64.complement x)
  | extremum (op : Extremum) (left : EvalWith a values x) (right : EvalWith b values y) :
      EvalWith (op.expr a b) values (op.denote x y)
  | binary (operation : Head head f) (left : EvalWith a values x) (right : EvalWith b values y) :
      EvalWith (.app (.app head a) b) values (f x y)
  | choose (op : Comparison) (type : ResultType) (left : EvalWith a values x) (right : EvalWith b values y)
      (branch : EvalWith (if op.denote x y then onTrue else onFalse) values value) :
      EvalWith (op.branch a b onTrue onFalse type) values value
  | chooseCompound (guard : CompoundGuard) (type : ResultType) {native : Lean.Expr → UInt64}
      (arguments : ∀ expression, expression ∈ guard.operands → EvalWith expression values (native expression))
      (branch : EvalWith (if guard.denote native then onTrue else onFalse) values value) :
      EvalWith (guard.branch type.expr onTrue onFalse) values value
  | chooseDependent (guard : DecidedGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo) {native : Lean.Expr → UInt64}
      (arguments : ∀ expression, expression ∈ guard.operands → EvalWith expression values (native expression))
      (branch : EvalWith (if guard.denote native then onTrue else onFalse) (.unit :: values) value) :
      EvalWith (guard.dependentBranch type.expr trueName falseName trueBi falseBi onTrue onFalse) values value
  | booleanWord (expression : BooleanLocal) {native : Lean.Expr → UInt64} {booleans : LeanExe.Source.Scalar.BooleanEnvironment}
      (variables : expression.VariablesMean values booleans)
      (arguments : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) values
        (Bool.toUInt64 (expression.denote native booleans))
  | letBoolean (expression : BooleanLocal) {native : Lean.Expr → UInt64} {booleans : LeanExe.Source.Scalar.BooleanEnvironment}
      (variables : expression.VariablesMean values booleans)
      (arguments : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand))
      (body : EvalWith b (.boolean (expression.denote native booleans) :: values) value) :
      EvalWith (.letE name (.const ``Bool []) expression.expr b nondep) values value
  | idBindBoolean (action : BooleanAction) (type : ResultType) {native : Lean.Expr → UInt64} {booleans : LeanExe.Source.Scalar.BooleanEnvironment}
      (variables : action.leaf.VariablesMean values booleans)
      (arguments : ∀ operand, operand ∈ action.leaf.operands → EvalWith operand values (native operand))
      (body : EvalWith b (.boolean (action.leaf.denote native booleans) :: values) value) :
      EvalWith (BooleanIdentity.bind name bi action.expr b type.expr) values value
  | chooseBoolean (guard : BooleanLocalGuard) (type : ResultType)
      {native : Lean.Expr → UInt64} {booleans : LeanExe.Source.Scalar.BooleanEnvironment}
      (variables : guard.value.VariablesMean values booleans)
      (arguments : ∀ operand, operand ∈ guard.value.operands → EvalWith operand values (native operand))
      (branch : EvalWith (if guard.value.denote native booleans then t else e) values value) :
      EvalWith (guard.branch type.expr t e) values value
  | chooseBooleanDependent (guard : BooleanLocalGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      {native : Lean.Expr → UInt64} {booleans : LeanExe.Source.Scalar.BooleanEnvironment}
      (variables : guard.value.VariablesMean values booleans)
      (arguments : ∀ operand, operand ∈ guard.value.operands → EvalWith operand values (native operand))
      (branch : EvalWith (if guard.value.denote native booleans then t else e) (.unit :: values) value) :
      EvalWith (guard.dependentBranch type.expr trueName falseName trueBi falseBi t e) values value
  | letE (value : EvalWith a values x) (body : EvalWith b (.word x :: values) y) :
      EvalWith (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (type : ResultType) (body : EvalWith e values value) : EvalWith (Identity.run e type) values value
  | idPure (type : ResultType) (body : EvalWith e values value) : EvalWith (Identity.pure e type) values value
  | idBind (input output : ResultType) (value : EvalWith a values x) (body : EvalWith b (.word x :: values) y) :
      EvalWith (Identity.bind name bi a b input output) values y
  | applyBoolean (expression : BooleanLocal) {native : Lean.Expr → UInt64} {booleans : LeanExe.Source.Scalar.BooleanEnvironment}
      (function : values[index]? = some (.booleanFunction f))
      (variables : expression.VariablesMean values booleans)
      (arguments : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand)) :
      EvalWith (.app (.bvar index) expression.expr) values (f (expression.denote native booleans))
  | apply (function : values[index]? = some (.function false f)) (argument : EvalWith a values x) :
      EvalWith (.app (.bvar index) a) values (f x)
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values) (f x))
      (body : EvalWith b (.function false f :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values value
  | letPredicateFn (expression : BooleanLocal) (type : BooleanType)
      {native : UInt64 → Lean.Expr → UInt64} {booleans : UInt64 → BooleanEnvironment}
      (variables : ∀ x, expression.VariablesMean (.word x :: values) (booleans x))
      (arguments : ∀ x operand, operand ∈ expression.operands →
        EvalWith operand (.word x :: values) (native x operand))
      (body : EvalWith b (.predicateFunction
        (fun x => expression.denote (native x) (booleans x)) :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep) values value
  | letBooleanFn (type : ResultType)
      (function : ∀ x, EvalWith a (.boolean x :: values) (f x))
      (body : EvalWith b (.booleanFunction f :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) a paramBi) b nondep) values value
  | unitApply (unitForm : UnitSyntax) (function : values[index]? = some (.function true f)) (argument : EvalWith a values x) :
      EvalWith (.app (.app (.bvar index) unitForm.value) a) values (f x)
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax)
      (function : ∀ x, EvalWith a (.word x :: .unit :: values) (f x))
      (body : EvalWith b (.function true f :: values) value) :
      EvalWith (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep) values value
  | binaryApply (function : values[index]? = some (.binaryFunction f))
      (first : EvalWith a values x) (second : EvalWith b values y) :
      EvalWith (.app (.app (.bvar index) a) b) values (f x y)
  | letBinaryFn (type : ResultType)
      (function : ∀ x y, EvalWith a (.word y :: .word x :: values) (f x y))
      (body : EvalWith b (.binaryFunction f :: values) value) :
      EvalWith (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep) values value
  | manyApply (call : ManyCall) {native : Lean.Expr → UInt64}
      (function : values[call.index]? = some (.manyFunction call.arity f))
      (arguments : ∀ operand, operand ∈ call.arguments → EvalWith operand values (native operand)) :
      EvalWith call.expr values (f (call.arguments.map native))
  | letManyFn (shape : ManyFunction)
      (function : ∀ arguments : List UInt64, arguments.length = shape.arity →
        EvalWith shape.body (arguments.reverse.map Value.word ++ values) (f arguments))
      (body : EvalWith b (.manyFunction shape.arity f :: values) value) :
      EvalWith (shape.bind name b nondep) values value
  | range (countValue : EvalWith count values stop) (initialValue : EvalWith initial values start)
      (yielding : Range.YieldScalar stepBody scalarBody)
      (steps : ∀ index value, EvalWith scalarBody (.word value :: .natural index :: values) (step index value)) :
      EvalWith (Range.call count initial indexName accumulatorName indexBi accumulatorBi stepBody)
        values (Range.iterate step stop.toNat 0 start)
  | idLet (body : EvalWith (.letE name type a b nondep) values value) :
      EvalWith (idLetExpr name type a b nondep) values value
  | ofNatTyped (numberMeaning : NaturalLiteral n numeral)
      (instanceMeaning : TypedLiteralInstance n type evidence) :
      EvalWith (typedLiteralExpr type numeral evidence) values (UInt64.ofNat n)
  | metadata (body : EvalWith e values value) : EvalWith (.mdata data e) values value

/-- Syntactic support, defined without inspecting compiler output. -/
inductive SupportedWith : List BindingKind → Lean.Expr → Prop where
  | var (h : types[index]? = some .word) : SupportedWith types (.bvar index)
  | natural (h : types[index]? = some .natural) :
      SupportedWith types (.app (.const ``UInt64.ofNat levels) (.bvar index))
  | literal : SupportedWith types (.app (.const ``UInt64.ofNat levels) (.lit (.natVal n)))
  | ofNat : SupportedWith types (literalExpr n)
  | ofNatInstance (instanceMeaning : LiteralInstance n 0 evidence) :
      SupportedWith types (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) (.lit (.natVal n))) evidence)
  | naturalLiteral (numberMeaning : NaturalLiteral n numeral) :
      SupportedWith types (.app (.const ``UInt64.ofNat levels) numeral)
  | ofNatNatural (numberMeaning : NaturalLiteral n numeral) (instanceMeaning : LiteralInstance n 0 evidence) :
      SupportedWith types (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``UInt64 [])) numeral) evidence)
  | complement (head : ComplementHead operation) (argument : SupportedWith types a) :
      SupportedWith types (.app operation a)
  | extremum (op : Extremum) (left : SupportedWith types a) (right : SupportedWith types b) :
      SupportedWith types (op.expr a b)
  | binary (operation : Head head f) (left : SupportedWith types a) (right : SupportedWith types b) :
      SupportedWith types (.app (.app head a) b)
  | choose (op : Comparison) (type : ResultType) (left : SupportedWith types a) (right : SupportedWith types b)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (op.branch a b t e type)
  | chooseCompound (guard : CompoundGuard) (type : ResultType)
      (arguments : ∀ expression, expression ∈ guard.operands → SupportedWith types expression)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (guard.branch type.expr t e)
  | chooseDependent (guard : DecidedGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      (arguments : ∀ expression, expression ∈ guard.operands → SupportedWith types expression)
      (onTrue : SupportedWith (.unit :: types) t) (onFalse : SupportedWith (.unit :: types) e) :
      SupportedWith types (guard.dependentBranch type.expr trueName falseName trueBi falseBi t e)
  | booleanWord (expression : BooleanLocal)
      (variables : expression.VariablesTyped types)
      (arguments : ∀ operand, operand ∈ expression.operands → SupportedWith types operand) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) expression.expr)
  | letBoolean (expression : BooleanLocal)
      (variables : expression.VariablesTyped types)
      (arguments : ∀ operand, operand ∈ expression.operands → SupportedWith types operand)
      (body : SupportedWith (.boolean :: types) b) :
      SupportedWith types (.letE name (.const ``Bool []) expression.expr b nondep)
  | idBindBoolean (action : BooleanAction) (type : ResultType)
      (variables : action.leaf.VariablesTyped types)
      (arguments : ∀ operand, operand ∈ action.leaf.operands → SupportedWith types operand)
      (body : SupportedWith (.boolean :: types) b) :
      SupportedWith types (BooleanIdentity.bind name bi action.expr b type.expr)
  | chooseBoolean (guard : BooleanLocalGuard) (type : ResultType)
      (variables : guard.value.VariablesTyped types)
      (arguments : ∀ operand, operand ∈ guard.value.operands → SupportedWith types operand)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (guard.branch type.expr t e)
  | chooseBooleanDependent (guard : BooleanLocalGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      (variables : guard.value.VariablesTyped types)
      (arguments : ∀ operand, operand ∈ guard.value.operands → SupportedWith types operand)
      (onTrue : SupportedWith (.unit :: types) t) (onFalse : SupportedWith (.unit :: types) e) :
      SupportedWith types (guard.dependentBranch type.expr trueName falseName trueBi falseBi t e)
  | letE (value : SupportedWith types a) (body : SupportedWith (.word :: types) b) :
      SupportedWith types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (type : ResultType) (body : SupportedWith types e) : SupportedWith types (Identity.run e type)
  | idPure (type : ResultType) (body : SupportedWith types e) : SupportedWith types (Identity.pure e type)
  | idBind (input output : ResultType) (value : SupportedWith types a) (body : SupportedWith (.word :: types) b) :
      SupportedWith types (Identity.bind name bi a b input output)
  | applyBoolean (expression : BooleanLocal) (function : types[index]? = some .booleanFunction)
      (variables : expression.VariablesTyped types)
      (arguments : ∀ operand, operand ∈ expression.operands → SupportedWith types operand) :
      SupportedWith types (.app (.bvar index) expression.expr)
  | apply (function : types[index]? = some (.function false)) (argument : SupportedWith types a) :
      SupportedWith types (.app (.bvar index) a)
  | letFn (type : ResultType) (function : SupportedWith (.word :: types) a)
      (body : SupportedWith (.function false :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (variables : expression.VariablesTyped (.word :: types))
      (arguments : ∀ operand, operand ∈ expression.operands → SupportedWith (.word :: types) operand)
      (body : SupportedWith (.predicateFunction :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep)
  | letBooleanFn (type : ResultType) (function : SupportedWith (.boolean :: types) a)
      (body : SupportedWith (.booleanFunction :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) a paramBi) b nondep)
  | unitApply (unitForm : UnitSyntax) (function : types[index]? = some (.function true)) (argument : SupportedWith types a) :
      SupportedWith types (.app (.app (.bvar index) unitForm.value) a)
  | letUnitFn (type : ResultType) (unitForm : UnitSyntax) (function : SupportedWith (.word :: .unit :: types) a)
      (body : SupportedWith (.function true :: types) b) :
      SupportedWith types (.letE name
        (.forallE unitTypeName unitForm.type
          (.forallE typeName (.const ``UInt64 []) type.expr typeBi) unitTypeBi)
        (.lam unitName unitForm.type
          (.lam paramName (.const ``UInt64 []) a paramBi) unitBi) b nondep)
  | binaryApply (function : types[index]? = some .binaryFunction)
      (first : SupportedWith types a) (second : SupportedWith types b) :
      SupportedWith types (.app (.app (.bvar index) a) b)
  | letBinaryFn (type : ResultType) (function : SupportedWith (.word :: .word :: types) a)
      (body : SupportedWith (.binaryFunction :: types) b) :
      SupportedWith types (.letE name
        (.forallE firstTypeName (.const ``UInt64 [])
          (.forallE secondTypeName (.const ``UInt64 []) type.expr secondTypeBi) firstTypeBi)
        (.lam firstName (.const ``UInt64 [])
          (.lam secondName (.const ``UInt64 []) a secondBi) firstBi) b nondep)
  | manyApply (call : ManyCall)
      (function : types[call.index]? = some (.manyFunction call.arity))
      (arguments : ∀ operand, operand ∈ call.arguments → SupportedWith types operand) :
      SupportedWith types call.expr
  | letManyFn (shape : ManyFunction)
      (function : SupportedWith (List.replicate shape.arity .word ++ types) shape.body)
      (body : SupportedWith (.manyFunction shape.arity :: types) b) :
      SupportedWith types (shape.bind name b nondep)
  | idLet (body : SupportedWith types (.letE name type a b nondep)) :
      SupportedWith types (idLetExpr name type a b nondep)
  | ofNatTyped (numberMeaning : NaturalLiteral n numeral)
      (instanceMeaning : TypedLiteralInstance n type evidence) :
      SupportedWith types (typedLiteralExpr type numeral evidence)
  | metadata (body : SupportedWith types e) : SupportedWith types (.mdata data e)

theorem SupportedWith.evaluates {types : List BindingKind} {expr : Lean.Expr}
    (h : SupportedWith types expr) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ value, EvalWith expr values value := by
  classical
  induction h generalizing values with
  | var hi =>
    obtain ⟨value, hv⟩ := word_lookup typed hi
    exact ⟨value, .var hv⟩
  | natural hi =>
    obtain ⟨value, hv⟩ := natural_lookup typed hi
    exact ⟨UInt64.ofNat value, .natural hv⟩
  | literal => exact ⟨_, .literal⟩
  | ofNat => exact ⟨_, .ofNat⟩
  | ofNatInstance evidence => exact ⟨_, .ofNatInstance evidence⟩
  | naturalLiteral numeral => exact ⟨_, .naturalLiteral numeral⟩
  | ofNatNatural numeral evidence => exact ⟨_, .ofNatNatural numeral evidence⟩
  | complement head _ ih =>
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨UInt64.complement x, .complement head hx⟩
  | extremum op _ _ ihl ihr =>
    obtain ⟨x, hx⟩ := ihl values typed
    obtain ⟨y, hy⟩ := ihr values typed
    exact ⟨op.denote x y, .extremum op hx hy⟩
  | binary op _ _ ihl ihr =>
    obtain ⟨x, hx⟩ := ihl values typed
    obtain ⟨y, hy⟩ := ihr values typed
    exact ⟨_, .binary op hx hy⟩
  | choose op type _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨x, hx⟩ := ihl values typed
    obtain ⟨y, hy⟩ := ihr values typed
    cases flag : op.denote x y with
    | false =>
      obtain ⟨value, hv⟩ := ihe values typed
      exact ⟨value, .choose op type hx hy (by simpa [flag] using hv)⟩
    | true =>
      obtain ⟨value, hv⟩ := iht values typed
      exact ⟨value, .choose op type hx hy (by simpa [flag] using hv)⟩
  | chooseCompound guard type _ _ _ ihArgs iht ihe =>
    let native : Lean.Expr → UInt64 := fun expression =>
      if member : expression ∈ guard.operands then (ihArgs expression member values typed).choose else 0
    have meanings : ∀ expression, expression ∈ guard.operands → EvalWith expression values (native expression) := by
      intro expression member
      simpa [native, member] using (ihArgs expression member values typed).choose_spec
    cases flag : guard.denote native with
    | false =>
      obtain ⟨value, hv⟩ := ihe values typed
      exact ⟨value, .chooseCompound guard type meanings (by simpa [flag] using hv)⟩
    | true =>
      obtain ⟨value, hv⟩ := iht values typed
      exact ⟨value, .chooseCompound guard type meanings (by simpa [flag] using hv)⟩
  | chooseDependent guard type tn fn tb fb _ _ _ ihArgs iht ihe =>
    let native : Lean.Expr → UInt64 := fun expression =>
      if member : expression ∈ guard.operands then (ihArgs expression member values typed).choose else 0
    have meanings : ∀ expression, expression ∈ guard.operands → EvalWith expression values (native expression) := by
      intro expression member
      simpa only [native, dite_eq_left member] using (ihArgs expression member values typed).choose_spec
    cases flag : guard.denote native with
    | false =>
      obtain ⟨value, hv⟩ := ihe (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseDependent guard type tn fn tb fb meanings (by simpa [flag] using hv)⟩
    | true =>
      obtain ⟨value, hv⟩ := iht (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseDependent guard type tn fn tb fb meanings (by simpa [flag] using hv)⟩
  | booleanWord expression variables _ ihArgs =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values typed
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ expression.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    exact ⟨Bool.toUInt64 (expression.denote native booleans), .booleanWord expression hbooleans meanings⟩
  | letBoolean expression variables _ _ ihArgs ihb =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values typed
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ expression.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    obtain ⟨result, body⟩ := ihb (.boolean (expression.denote native booleans) :: values)
      (by simp [Value.kind, typed])
    exact ⟨result, .letBoolean expression hbooleans meanings body⟩
  | idBindBoolean action type variables _ _ ihArgs ihb =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values typed
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ action.leaf.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ action.leaf.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    obtain ⟨result, body⟩ := ihb (.boolean (action.leaf.denote native booleans) :: values)
      (by simp [Value.kind, typed])
    exact ⟨result, .idBindBoolean action type hbooleans meanings body⟩
  | chooseBoolean guard type variables _ _ _ ihArgs iht ihe =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values typed
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ guard.value.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ guard.value.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    cases flag : guard.value.denote native booleans with
    | false =>
      obtain ⟨value, body⟩ := ihe values typed
      exact ⟨value, .chooseBoolean guard type hbooleans meanings (by simpa [flag] using body)⟩
    | true =>
      obtain ⟨value, body⟩ := iht values typed
      exact ⟨value, .chooseBoolean guard type hbooleans meanings (by simpa [flag] using body)⟩
  | chooseBooleanDependent guard type tn fn tb fb variables _ _ _ ihArgs iht ihe =>
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values typed
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ guard.value.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ guard.value.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    cases flag : guard.value.denote native booleans with
    | false =>
      obtain ⟨value, body⟩ := ihe (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseBooleanDependent guard type tn fn tb fb hbooleans meanings (by simpa [flag] using body)⟩
    | true =>
      obtain ⟨value, body⟩ := iht (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseBooleanDependent guard type tn fn tb fb hbooleans meanings (by simpa [flag] using body)⟩
  | letE _ _ ihv ihb =>
    obtain ⟨x, hx⟩ := ihv values typed
    obtain ⟨y, hy⟩ := ihb (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .letE hx hy⟩
  | idRun type _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idRun type hv⟩
  | idPure type _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idPure type hv⟩
  | idBind input output _ _ ihv ihb =>
    obtain ⟨x, hx⟩ := ihv values typed
    obtain ⟨y, hy⟩ := ihb (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨y, .idBind input output hx hy⟩
  | applyBoolean expression present variables _ ihArgs =>
    obtain ⟨f, hf⟩ := booleanFunction_lookup typed present
    obtain ⟨booleans, hbooleans⟩ := variables.evaluates values typed
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ expression.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ expression.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    exact ⟨f (expression.denote native booleans), .applyBoolean expression hf hbooleans meanings⟩
  | apply present _ ih =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨f x, .apply hf hx⟩
  | letFn type _ _ ihf ihb =>
    have total := fun x => ihf (.word x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letFn type (fun x => (total x).choose_spec) hv⟩
  | letPredicateFn expression type variables _ _ ihArgs ihb =>
    have environments := fun x => variables.evaluates (.word x :: values)
      (by simp [Value.kind, typed])
    let booleans := fun x => (environments x).choose
    let native : UInt64 → Lean.Expr → UInt64 := fun x operand =>
      if member : operand ∈ expression.operands then
        (ihArgs operand member (.word x :: values) (by simp [Value.kind, typed])).choose else 0
    have meanings : ∀ x operand, operand ∈ expression.operands →
        EvalWith operand (.word x :: values) (native x operand) := by
      intro x operand member
      simpa only [native, dite_eq_left member] using
        (ihArgs operand member (.word x :: values) (by simp [Value.kind, typed])).choose_spec
    obtain ⟨value, hv⟩ := ihb (.predicateFunction
      (fun x => expression.denote (native x) (booleans x)) :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letPredicateFn expression type (fun x => (environments x).choose_spec) meanings hv⟩
  | letBooleanFn type _ _ ihf ihb =>
    have total := fun x => ihf (.boolean x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.booleanFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBooleanFn type (fun x => (total x).choose_spec) hv⟩
  | unitApply unitForm present _ ih =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨f x, .unitApply unitForm hf hx⟩
  | letUnitFn type unitForm _ _ ihf ihb =>
    have total := fun x => ihf (.word x :: .unit :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function true f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letUnitFn type unitForm (fun x => (total x).choose_spec) hv⟩
  | binaryApply present _ _ ihFirst ihSecond =>
    obtain ⟨f, hf⟩ := binaryFunction_lookup typed present
    obtain ⟨x, hx⟩ := ihFirst values typed
    obtain ⟨y, hy⟩ := ihSecond values typed
    exact ⟨f x y, .binaryApply hf hx hy⟩
  | letBinaryFn type _ _ ihf ihb =>
    have total := fun x y => ihf (.word y :: .word x :: values) (by simp [Value.kind, typed])
    let f := fun x y => (total x y).choose
    obtain ⟨value, hv⟩ := ihb (.binaryFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBinaryFn type (fun x y => (total x y).choose_spec) hv⟩
  | manyApply call present _ ihArgs =>
    obtain ⟨f, hf⟩ := manyFunction_lookup typed present
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ call.arguments then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ call.arguments → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    exact ⟨f (call.arguments.map native), .manyApply call hf meanings⟩
  | letManyFn shape _ _ ihf ihb =>
    have total := fun (arguments : List UInt64) (len : arguments.length = shape.arity) =>
      ihf (arguments.reverse.map Value.word ++ values)
        (by simp [List.map_map, Function.comp_def, Value.kind, List.map_const', len, typed])
    let f : List UInt64 → UInt64 := fun arguments =>
      if len : arguments.length = shape.arity then (total arguments len).choose else 0
    have meanings : ∀ arguments : List UInt64, arguments.length = shape.arity →
        EvalWith shape.body (arguments.reverse.map Value.word ++ values) (f arguments) := by
      intro arguments len
      simpa [f, len] using (total arguments len).choose_spec
    obtain ⟨value, hv⟩ := ihb (.manyFunction shape.arity f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letManyFn shape meanings hv⟩
  | idLet _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .idLet hv⟩
  | ofNatTyped numeral evidence => exact ⟨_, .ofNatTyped numeral evidence⟩
  | metadata _ ih =>
    obtain ⟨value, hv⟩ := ih values typed
    exact ⟨value, .metadata hv⟩

theorem EvalWith.not_unit {expression values value} (evaluated : EvalWith expression values value) (unitForm : UnitSyntax) :
    expression ≠ unitForm.value := by
  intro same
  subst expression
  cases unitForm <;> cases evaluated

theorem SupportedWith.not_unit {types expression} (supported : SupportedWith types expression) (unitForm : UnitSyntax) :
    expression ≠ unitForm.value := by
  intro same
  subst expression
  cases unitForm <;> cases supported

/-- Public scalar entry semantics: parameters contain words; closures are internal. -/
abbrev Eval (expr : Lean.Expr) (values : List UInt64) (value : UInt64) : Prop :=
  EvalWith expr (values.map Value.word) value

/-- Public declarations begin with only word parameters. -/
abbrev Supported (arity : Nat) (expr : Lean.Expr) : Prop :=
  SupportedWith (List.replicate arity .word) expr

theorem Supported.evaluates {arity : Nat} {expr : Lean.Expr}
    (h : Supported arity expr) (values : List UInt64) (len : values.length = arity) :
    ∃ value, Eval expr values value := by
  apply SupportedWith.evaluates h
  simp [List.map_map, Function.comp_def, Value.kind, List.map_const', len]

end LeanExe.Source.Scalar
