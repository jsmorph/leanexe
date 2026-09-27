import LeanExe.Source.ScalarBooleanSelected
import LeanExe.Source.ScalarBooleanRelated
import LeanExe.Source.ScalarBooleanJoined
import LeanExe.Source.ScalarBooleanNegated
import LeanExe.Source.ScalarBooleanWrapped
import LeanExe.Source.ScalarBooleanScopeGuard
import LeanExe.Source.ScalarBooleanHelper
import LeanExe.Source.ScalarBooleanInput
import LeanExe.Source.ScalarBooleanConditionInputs
import LeanExe.Source.ScalarBooleanPropositionChoiceForm
import LeanExe.Source.ScalarBooleanChoiceForm
import LeanExe.Source.ScalarBooleanEqualityForm
import LeanExe.Source.ScalarPredicateInput
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
  | naturalToUInt64 (h : values[index]? = some (.natural value)) :
      EvalWith (.app (.const ``Nat.toUInt64 []) (.bvar index)) values value.toUInt64
  | naturalLiteralToUInt64 (numberMeaning : NaturalLiteral n numeral) :
      EvalWith (.app (.const ``Nat.toUInt64 []) numeral) values n.toUInt64
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
  | letBoolean (bound : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag))
      (body : EvalWith b (.boolean flag :: values) value) :
      EvalWith (.letE name (.const ``Bool []) a b nondep) values value
  | idBindBoolean (action : BooleanAction) (type : ResultType)
      (bound : EvalWith (.app (.const ``Bool.toUInt64 []) action.expr) values (Bool.toUInt64 flag))
      (body : EvalWith b (.boolean flag :: values) value) :
      EvalWith (BooleanIdentity.bind name bi action.expr b type.expr) values value
  | chooseScope (guard : BooleanScopeGuard) (type : ResultType)
      (condition : EvalWith guard.operand values (Bool.toUInt64 flag))
      (branch : EvalWith (if flag then t else e) values value) :
      EvalWith (guard.branch type.expr t e) values value
  | chooseScopeDependent (guard : BooleanScopeGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueInfo falseInfo : Lean.BinderInfo)
      (condition : EvalWith guard.operand values (Bool.toUInt64 flag))
      (branch : EvalWith (if flag then t else e) (.unit :: values) value) :
      EvalWith (guard.dependentBranch type.expr trueName falseName trueInfo falseInfo t e) values value
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
  | chooseBooleanPredicate (guard : BooleanLocalGuard) (type : ResultType)
      (member : index ∈ guard.value.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      {native : BooleanLocal → Bool}
      (arguments : ∀ input, input ∈ guard.form.inputs →
        EvalWith (.app (.const ``Bool.toUInt64 []) input.expr) values (Bool.toUInt64 (native input)))
      (branch : EvalWith (if guard.form.denoteInputs native then t else e) values value) :
      EvalWith (guard.branch type.expr t e) values value
  | chooseBooleanPredicateDependent (guard : BooleanLocalGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      (member : index ∈ guard.value.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      {native : BooleanLocal → Bool}
      (arguments : ∀ input, input ∈ guard.form.inputs →
        EvalWith (.app (.const ``Bool.toUInt64 []) input.expr) values (Bool.toUInt64 (native input)))
      (branch : EvalWith (if guard.form.denoteInputs native then t else e) (.unit :: values) value) :
      EvalWith (guard.dependentBranch type.expr trueName falseName trueBi falseBi t e) values value
  | letE (value : EvalWith a values x) (body : EvalWith b (.word x :: values) y) :
      EvalWith (.letE name (.const ``UInt64 []) a b nondep) values y
  | idRun (type : ResultType) (body : EvalWith e values value) : EvalWith (Identity.run e type) values value
  | idPure (type : ResultType) (body : EvalWith e values value) : EvalWith (Identity.pure e type) values value
  | idBind (input output : ResultType) (value : EvalWith a values x) (body : EvalWith b (.word x :: values) y) :
      EvalWith (Identity.bind name bi a b input output) values y
  | applyBoolean (function : values[index]? = some (.booleanFunction f))
      (argument : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.bvar index) a) values (f flag)
  | booleanPropositionWord (form : BooleanChoiceForm) (negations : Nat)
      (guard : PropositionGuard) (yes no : BooleanLocal)
      (member : index ∈ yes.functions ++ no.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      {native : Lean.Expr → UInt64}
      (operands : ∀ operand, operand ∈ guard.operands → EvalWith operand values (native operand))
      (branch : EvalWith (.app (.const ``Bool.toUInt64 [])
        (if guard.denote native then yes.expr else no.expr)) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (form.proposition negations guard yes no).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations flag))
  | booleanChoiceWord (form : BooleanChoiceForm) (negations : Nat) (unequal : Bool)
      (left right yes no : BooleanLocal)
      (member : index ∈ left.functions ++ (right.functions ++ (yes.functions ++ no.functions)))
      (function : values[index]? = some (.booleanPredicateFunction f))
      (first : EvalWith (.app (.const ``Bool.toUInt64 []) left.expr) values (Bool.toUInt64 a))
      (second : EvalWith (.app (.const ``Bool.toUInt64 []) right.expr) values (Bool.toUInt64 b))
      (branch : EvalWith (.app (.const ``Bool.toUInt64 [])
        (if booleanRelationDecision unequal a b then yes.expr else no.expr)) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (form.local negations unequal left right yes no).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations flag))
  | booleanEqualityWord (form : BooleanEqualityForm) (negations : Nat) (unequal : Bool)
      (left right : BooleanLocal) (member : index ∈ left.functions ++ right.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      (first : EvalWith (.app (.const ``Bool.toUInt64 []) left.expr) values (Bool.toUInt64 a))
      (second : EvalWith (.app (.const ``Bool.toUInt64 []) right.expr) values (Bool.toUInt64 b)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (form.local negations unequal left right).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations (form.denote unequal a b)))
  | booleanBindingWord (negations : Nat) (name : Lean.Name) (form : BooleanBindingForm)
      (value body : BooleanLocal) (type : BooleanType)
      (member : index ∈ value.functions ++ booleanLetVariables body.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      (bound : EvalWith (.app (.const ``Bool.toUInt64 []) value.expr) values (Bool.toUInt64 flag))
      (result : EvalWith (.app (.const ``Bool.toUInt64 []) body.expr)
        (.boolean flag :: values) (Bool.toUInt64 outcome)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (BooleanLocal.binding negations name form value body type).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations outcome))
  | wordBindingBooleanWord (negations : Nat) (name : Lean.Name) (form : BooleanBindingForm)
      (value : Lean.Expr) (body : BooleanLocal) (type : ResultType)
      (member : index ∈ booleanLetVariables body.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      (bound : EvalWith value values flag)
      (result : EvalWith (.app (.const ``Bool.toUInt64 []) body.expr)
        (.word flag :: values) (Bool.toUInt64 outcome)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (BooleanLocal.wordBinding negations name form value body type).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations outcome))
  | booleanWrappedWord (negations : Nat) (wrapper : BooleanWrapper) (body : BooleanLocal)
      (member : index ∈ body.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      (inner : EvalWith (.app (.const ``Bool.toUInt64 []) body.expr) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (BooleanLocal.wrapped negations wrapper body).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations (wrapper.denote flag)))
  | booleanJunctionWord (negations : Nat) (op : Junction) (left right : BooleanLocal)
      (member : index ∈ left.functions ++ right.functions)
      (function : values[index]? = some (.booleanPredicateFunction f))
      (first : EvalWith (.app (.const ``Bool.toUInt64 []) left.expr) values (Bool.toUInt64 a))
      (second : EvalWith (.app (.const ``Bool.toUInt64 []) right.expr) values (Bool.toUInt64 b)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) (BooleanLocal.junction negations op left right).expr)
        values (Bool.toUInt64 (GuardNegation.denote negations (op.denote a b)))
  | applyBooleanPredicateWord (negations : Nat)
      (function : values[index]? = some (.booleanPredicateFunction f))
      (argument : EvalWith (.app (.const ``Bool.toUInt64 []) a) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 [])
        (BooleanGuardNegation.expr negations (.app (.bvar index) a))) values
        (Bool.toUInt64 (GuardNegation.denote negations (f flag)))
  | apply (function : values[index]? = some (.function false f)) (argument : EvalWith a values x) :
      EvalWith (.app (.bvar index) a) values (f x)
  | letFn (type : ResultType)
      (function : ∀ x, EvalWith a (.word x :: values) (f x))
      (body : EvalWith b (.function false f :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep) values value
  | letPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr)
        (.word x :: values) (Bool.toUInt64 (f x)))
      (body : EvalWith b (.predicateFunction f :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep) values value
  | letBooleanPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr)
        (.boolean x :: values) (Bool.toUInt64 (f x)))
      (body : EvalWith b (.booleanPredicateFunction f :: values) value) :
      EvalWith (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) expression.expr paramBi) b nondep) values value
  | scopedSelection (selected : BooleanSelected)
      (condition : EvalWith (.app (.const ``Bool.toUInt64 []) selected.selection.condition) values (Bool.toUInt64 flag))
      (branch : EvalWith (.app (.const ``Bool.toUInt64 []) (if flag then selected.selection.yes else selected.selection.no)) values (Bool.toUInt64 result)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) selected.expr) values (Bool.toUInt64 result)
  | scopedEquality (related : BooleanRelated)
      (left : EvalWith (.app (.const ``Bool.toUInt64 []) related.relation.left) values (Bool.toUInt64 a))
      (right : EvalWith (.app (.const ``Bool.toUInt64 []) related.relation.right) values (Bool.toUInt64 b)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) related.expr) values (Bool.toUInt64 (related.relation.denote a b))
  | scopedJunction (joined : BooleanJoined)
      (left : EvalWith (.app (.const ``Bool.toUInt64 []) joined.left) values (Bool.toUInt64 a))
      (right : EvalWith (.app (.const ``Bool.toUInt64 []) joined.right) values (Bool.toUInt64 b)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) joined.expr) values (Bool.toUInt64 (joined.operation.denote a b))
  | scopedNegation (negated : BooleanNegated)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) negated.body) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) negated.expr) values (Bool.toUInt64 (!flag))
  | scopedWrapper (wrapped : BooleanWrapped)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) wrapped.body) values (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) wrapped.expr) values (Bool.toUInt64 (wrapped.wrapper.denote flag))
  | scopedPredicate (helper : BooleanHelper false)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) helper.body.expr)
        (.word x :: values) (Bool.toUInt64 (f x)))
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) helper.continuation)
        (.predicateFunction f :: values) (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) helper.expr) values (Bool.toUInt64 flag)
  | scopedBooleanPredicate (helper : BooleanHelper true)
      (function : ∀ x, EvalWith (.app (.const ``Bool.toUInt64 []) helper.body.expr)
        (.boolean x :: values) (Bool.toUInt64 (f x)))
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) helper.continuation)
        (.booleanPredicateFunction f :: values) (Bool.toUInt64 flag)) :
      EvalWith (.app (.const ``Bool.toUInt64 []) helper.expr) values (Bool.toUInt64 flag)
  | predicateInput (input : ResultType) (result : BooleanType)
      (inner : EvalWith (predicateInputExpr input result name typeName paramName typeBi paramBi a b nondep) values outcome) :
      EvalWith (predicateInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep) values outcome
  | booleanInput (input : BooleanType) (result : Lean.Expr)
      (inner : EvalWith (booleanInputExpr input result name typeName paramName typeBi paramBi a b nondep) values outcome) :
      EvalWith (booleanInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep) values outcome
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
  | naturalToUInt64 (h : types[index]? = some .natural) :
      SupportedWith types (.app (.const ``Nat.toUInt64 []) (.bvar index))
  | naturalLiteralToUInt64 (numberMeaning : NaturalLiteral n numeral) :
      SupportedWith types (.app (.const ``Nat.toUInt64 []) numeral)
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
  | letBoolean (bound : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : SupportedWith (.boolean :: types) b) :
      SupportedWith types (.letE name (.const ``Bool []) a b nondep)
  | idBindBoolean (action : BooleanAction) (type : ResultType)
      (bound : SupportedWith types (.app (.const ``Bool.toUInt64 []) action.expr))
      (body : SupportedWith (.boolean :: types) b) :
      SupportedWith types (BooleanIdentity.bind name bi action.expr b type.expr)
  | chooseScope (guard : BooleanScopeGuard) (type : ResultType)
      (condition : SupportedWith types guard.operand)
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (guard.branch type.expr t e)
  | chooseScopeDependent (guard : BooleanScopeGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueInfo falseInfo : Lean.BinderInfo)
      (condition : SupportedWith types guard.operand)
      (onTrue : SupportedWith (.unit :: types) t) (onFalse : SupportedWith (.unit :: types) e) :
      SupportedWith types (guard.dependentBranch type.expr trueName falseName trueInfo falseInfo t e)
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
  | chooseBooleanPredicate (guard : BooleanLocalGuard) (type : ResultType)
      (member : index ∈ guard.value.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (arguments : ∀ input, input ∈ guard.form.inputs →
        SupportedWith types (.app (.const ``Bool.toUInt64 []) input.expr))
      (onTrue : SupportedWith types t) (onFalse : SupportedWith types e) :
      SupportedWith types (guard.branch type.expr t e)
  | chooseBooleanPredicateDependent (guard : BooleanLocalGuard) (type : ResultType)
      (trueName falseName : Lean.Name) (trueBi falseBi : Lean.BinderInfo)
      (member : index ∈ guard.value.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (arguments : ∀ input, input ∈ guard.form.inputs →
        SupportedWith types (.app (.const ``Bool.toUInt64 []) input.expr))
      (onTrue : SupportedWith (.unit :: types) t) (onFalse : SupportedWith (.unit :: types) e) :
      SupportedWith types (guard.dependentBranch type.expr trueName falseName trueBi falseBi t e)
  | letE (value : SupportedWith types a) (body : SupportedWith (.word :: types) b) :
      SupportedWith types (.letE name (.const ``UInt64 []) a b nondep)
  | idRun (type : ResultType) (body : SupportedWith types e) : SupportedWith types (Identity.run e type)
  | idPure (type : ResultType) (body : SupportedWith types e) : SupportedWith types (Identity.pure e type)
  | idBind (input output : ResultType) (value : SupportedWith types a) (body : SupportedWith (.word :: types) b) :
      SupportedWith types (Identity.bind name bi a b input output)
  | applyBoolean (function : types[index]? = some .booleanFunction)
      (argument : SupportedWith types (.app (.const ``Bool.toUInt64 []) a)) :
      SupportedWith types (.app (.bvar index) a)
  | booleanPropositionWord (form : BooleanChoiceForm) (negations : Nat)
      (guard : PropositionGuard) (yes no : BooleanLocal)
      (member : index ∈ yes.functions ++ no.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (operands : ∀ operand, operand ∈ guard.operands → SupportedWith types operand)
      (trueBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) yes.expr))
      (falseBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) no.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (form.proposition negations guard yes no).expr)
  | booleanChoiceWord (form : BooleanChoiceForm) (negations : Nat) (unequal : Bool)
      (left right yes no : BooleanLocal)
      (member : index ∈ left.functions ++ (right.functions ++ (yes.functions ++ no.functions)))
      (function : types[index]? = some .booleanPredicateFunction)
      (first : SupportedWith types (.app (.const ``Bool.toUInt64 []) left.expr))
      (second : SupportedWith types (.app (.const ``Bool.toUInt64 []) right.expr))
      (trueBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) yes.expr))
      (falseBranch : SupportedWith types (.app (.const ``Bool.toUInt64 []) no.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (form.local negations unequal left right yes no).expr)
  | booleanEqualityWord (form : BooleanEqualityForm) (negations : Nat) (unequal : Bool)
      (left right : BooleanLocal) (member : index ∈ left.functions ++ right.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (first : SupportedWith types (.app (.const ``Bool.toUInt64 []) left.expr))
      (second : SupportedWith types (.app (.const ``Bool.toUInt64 []) right.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (form.local negations unequal left right).expr)
  | booleanBindingWord (negations : Nat) (name : Lean.Name) (form : BooleanBindingForm)
      (value body : BooleanLocal) (type : BooleanType)
      (member : index ∈ value.functions ++ booleanLetVariables body.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (bound : SupportedWith types (.app (.const ``Bool.toUInt64 []) value.expr))
      (result : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) body.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (BooleanLocal.binding negations name form value body type).expr)
  | wordBindingBooleanWord (negations : Nat) (name : Lean.Name) (form : BooleanBindingForm)
      (value : Lean.Expr) (body : BooleanLocal) (type : ResultType)
      (member : index ∈ booleanLetVariables body.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (bound : SupportedWith types value)
      (result : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) body.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (BooleanLocal.wordBinding negations name form value body type).expr)
  | booleanWrappedWord (negations : Nat) (wrapper : BooleanWrapper) (body : BooleanLocal)
      (member : index ∈ body.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (inner : SupportedWith types (.app (.const ``Bool.toUInt64 []) body.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (BooleanLocal.wrapped negations wrapper body).expr)
  | booleanJunctionWord (negations : Nat) (op : Junction) (left right : BooleanLocal)
      (member : index ∈ left.functions ++ right.functions)
      (function : types[index]? = some .booleanPredicateFunction)
      (first : SupportedWith types (.app (.const ``Bool.toUInt64 []) left.expr))
      (second : SupportedWith types (.app (.const ``Bool.toUInt64 []) right.expr)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) (BooleanLocal.junction negations op left right).expr)
  | applyBooleanPredicateWord (negations : Nat)
      (function : types[index]? = some .booleanPredicateFunction)
      (argument : SupportedWith types (.app (.const ``Bool.toUInt64 []) a)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 [])
        (BooleanGuardNegation.expr negations (.app (.bvar index) a)))
  | apply (function : types[index]? = some (.function false)) (argument : SupportedWith types a) :
      SupportedWith types (.app (.bvar index) a)
  | letFn (type : ResultType) (function : SupportedWith (.word :: types) a)
      (body : SupportedWith (.function false :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) a paramBi) b nondep)
  | letPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) expression.expr))
      (body : SupportedWith (.predicateFunction :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``UInt64 []) type.expr typeBi)
        (.lam paramName (.const ``UInt64 []) expression.expr paramBi) b nondep)
  | letBooleanPredicateFn (expression : BooleanLocal) (type : BooleanType)
      (function : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) expression.expr))
      (body : SupportedWith (.booleanPredicateFunction :: types) b) :
      SupportedWith types (.letE name
        (.forallE typeName (.const ``Bool []) type.expr typeBi)
        (.lam paramName (.const ``Bool []) expression.expr paramBi) b nondep)
  | scopedSelection (selected : BooleanSelected)
      (condition : SupportedWith types (.app (.const ``Bool.toUInt64 []) selected.selection.condition))
      (yes : SupportedWith types (.app (.const ``Bool.toUInt64 []) selected.selection.yes))
      (no : SupportedWith types (.app (.const ``Bool.toUInt64 []) selected.selection.no)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) selected.expr)
  | scopedEquality (related : BooleanRelated)
      (left : SupportedWith types (.app (.const ``Bool.toUInt64 []) related.relation.left))
      (right : SupportedWith types (.app (.const ``Bool.toUInt64 []) related.relation.right)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) related.expr)
  | scopedJunction (joined : BooleanJoined)
      (left : SupportedWith types (.app (.const ``Bool.toUInt64 []) joined.left))
      (right : SupportedWith types (.app (.const ``Bool.toUInt64 []) joined.right)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) joined.expr)
  | scopedNegation (negated : BooleanNegated)
      (body : SupportedWith types (.app (.const ``Bool.toUInt64 []) negated.body)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) negated.expr)
  | scopedWrapper (wrapped : BooleanWrapped)
      (body : SupportedWith types (.app (.const ``Bool.toUInt64 []) wrapped.body)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) wrapped.expr)
  | scopedPredicate (helper : BooleanHelper false)
      (function : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) helper.body.expr))
      (body : SupportedWith (.predicateFunction :: types) (.app (.const ``Bool.toUInt64 []) helper.continuation)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) helper.expr)
  | scopedBooleanPredicate (helper : BooleanHelper true)
      (function : SupportedWith (.boolean :: types) (.app (.const ``Bool.toUInt64 []) helper.body.expr))
      (body : SupportedWith (.booleanPredicateFunction :: types) (.app (.const ``Bool.toUInt64 []) helper.continuation)) :
      SupportedWith types (.app (.const ``Bool.toUInt64 []) helper.expr)
  | predicateInput (input : ResultType) (result : BooleanType)
      (inner : SupportedWith types (predicateInputExpr input result name typeName paramName typeBi paramBi a b nondep)) :
      SupportedWith types (predicateInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep)
  | booleanInput (input : BooleanType) (result : Lean.Expr)
      (inner : SupportedWith types (booleanInputExpr input result name typeName paramName typeBi paramBi a b nondep)) :
      SupportedWith types (booleanInputExpr (.identity input) result name typeName paramName typeBi paramBi a b nondep)
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

set_option linter.unusedSimpArgs false in
theorem EvalWith.booleanConversion_result {argument : Lean.Expr} {values : List Value}
    {value : UInt64} (evaluation : EvalWith (.app (.const ``Bool.toUInt64 []) argument) values value) :
    ∃ flag : Bool, value = flag.toUInt64 := by
  generalize expressionEq : Lean.Expr.app (.const ``Bool.toUInt64 []) argument = expression at evaluation
  cases evaluation with
  | booleanWord | booleanBindingWord | wordBindingBooleanWord | booleanWrappedWord | booleanJunctionWord | booleanEqualityWord | booleanChoiceWord | booleanPropositionWord => exact ⟨_, rfl⟩
  | applyBooleanPredicateWord | scopedPredicate | scopedBooleanPredicate | scopedWrapper | scopedNegation | scopedJunction | scopedEquality | scopedSelection => exact ⟨_, rfl⟩
  | complement head _ => cases head <;> simp_all
  | extremum op _ _ => cases op <;> simp_all [Extremum.expr, Extremum.head]
  | manyApply call _ _ =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    simp [ManyCall.expr, ManyCall.index, Lean.Expr.getAppFn] at root
  | range =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    change Lean.Expr.const ``Bool.toUInt64 [] = .const ``ForIn.forIn [.zero, .zero, .zero, .zero] at root
    simp at root
  | _ =>
    simp_all [literalExpr, typedLiteralExpr, Comparison.branch, CompoundGuard.branch,
      DecidedGuard.dependentBranch, BooleanScopeGuard.branch, BooleanScopeGuard.dependentBranch,
      BooleanIdentity.bind, BooleanLocalGuard.branch,
      BooleanLocalGuard.dependentBranch, Identity.run, Identity.pure, Identity.bind,
      UnitSyntax.value, Extremum.expr, ManyFunction.bind, Range.call, Range.head,
      idLetExpr, predicateInputExpr, booleanInputExpr]


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
  | naturalToUInt64 hi =>
    obtain ⟨value, hv⟩ := natural_lookup typed hi
    exact ⟨value.toUInt64, .naturalToUInt64 hv⟩
  | naturalLiteralToUInt64 meaning => exact ⟨_, .naturalLiteralToUInt64 meaning⟩
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
  | letBoolean _ _ ihv ihb =>
    obtain ⟨encoded, hv⟩ := ihv values typed
    obtain ⟨flag, rfl⟩ := hv.booleanConversion_result
    obtain ⟨result, hb⟩ := ihb (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letBoolean hv hb⟩
  | idBindBoolean action type _ _ ihv ihb =>
    obtain ⟨encoded, hv⟩ := ihv values typed
    obtain ⟨flag, rfl⟩ := hv.booleanConversion_result
    obtain ⟨result, hb⟩ := ihb (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .idBindBoolean action type hv hb⟩
  | chooseScope guard type _ _ _ ihc iht ihe =>
    obtain ⟨encoded, evaluated⟩ := ihc values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨value, branch⟩ := ihe values typed
      exact ⟨value, .chooseScope guard type evaluated branch⟩
    | true =>
      obtain ⟨value, branch⟩ := iht values typed
      exact ⟨value, .chooseScope guard type evaluated branch⟩
  | chooseScopeDependent guard type tn fn ti fi _ _ _ ihc iht ihe =>
    obtain ⟨encoded, evaluated⟩ := ihc values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨value, branch⟩ := ihe (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseScopeDependent guard type tn fn ti fi evaluated branch⟩
    | true =>
      obtain ⟨value, branch⟩ := iht (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseScopeDependent guard type tn fn ti fi evaluated branch⟩
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
  | chooseBooleanPredicate guard type member present _ _ _ ihArgs iht ihe =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    have inputFlag : ∀ input, input ∈ guard.form.inputs →
        ∃ flag : Bool, EvalWith (.app (.const ``Bool.toUInt64 []) input.expr) values flag.toUInt64 := by
      intro input member
      obtain ⟨encoded, evaluated⟩ := ihArgs input member values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let native : BooleanLocal → Bool := fun input =>
      if member : input ∈ guard.form.inputs then (inputFlag input member).choose else false
    have meanings : ∀ input, input ∈ guard.form.inputs →
        EvalWith (.app (.const ``Bool.toUInt64 []) input.expr) values (native input).toUInt64 := by
      intro input member
      simpa only [native, dite_eq_left member] using (inputFlag input member).choose_spec
    cases result : guard.form.denoteInputs native with
    | false =>
      obtain ⟨value, evaluated⟩ := ihe values typed
      exact ⟨value, .chooseBooleanPredicate guard type member hf meanings
        (by simpa only [result, Bool.false_eq_true, ↓reduceIte] using evaluated)⟩
    | true =>
      obtain ⟨value, evaluated⟩ := iht values typed
      exact ⟨value, .chooseBooleanPredicate guard type member hf meanings
        (by simpa only [result, ↓reduceIte] using evaluated)⟩
  | chooseBooleanPredicateDependent guard type tn fn tb fb member present _ _ _ ihArgs iht ihe =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    have inputFlag : ∀ input, input ∈ guard.form.inputs →
        ∃ flag : Bool, EvalWith (.app (.const ``Bool.toUInt64 []) input.expr) values flag.toUInt64 := by
      intro input member
      obtain ⟨encoded, evaluated⟩ := ihArgs input member values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let native : BooleanLocal → Bool := fun input =>
      if member : input ∈ guard.form.inputs then (inputFlag input member).choose else false
    have meanings : ∀ input, input ∈ guard.form.inputs →
        EvalWith (.app (.const ``Bool.toUInt64 []) input.expr) values (native input).toUInt64 := by
      intro input member
      simpa only [native, dite_eq_left member] using (inputFlag input member).choose_spec
    cases result : guard.form.denoteInputs native with
    | false =>
      obtain ⟨value, evaluated⟩ := ihe (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseBooleanPredicateDependent guard type tn fn tb fb member hf meanings
        (by simpa only [result, Bool.false_eq_true, ↓reduceIte] using evaluated)⟩
    | true =>
      obtain ⟨value, evaluated⟩ := iht (.unit :: values) (by simp [Value.kind, typed])
      exact ⟨value, .chooseBooleanPredicateDependent guard type tn fn tb fb member hf meanings
        (by simpa only [result, ↓reduceIte] using evaluated)⟩
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
  | applyBoolean present _ ih =>
    obtain ⟨f, hf⟩ := booleanFunction_lookup typed present
    obtain ⟨argument, evaluated⟩ := ih values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨f flag, .applyBoolean hf evaluated⟩
  | booleanPropositionWord form negations guard yes no member present _ _ _ ihArgs iht ihe =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    let native : Lean.Expr → UInt64 := fun operand =>
      if member : operand ∈ guard.operands then (ihArgs operand member values typed).choose else 0
    have meanings : ∀ operand, operand ∈ guard.operands → EvalWith operand values (native operand) := by
      intro operand member
      simpa only [native, dite_eq_left member] using (ihArgs operand member values typed).choose_spec
    cases result : guard.denote native with
    | false =>
      obtain ⟨value, evaluated⟩ := ihe values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨Bool.toUInt64 (GuardNegation.denote negations flag),
        .booleanPropositionWord form negations guard yes no member hf meanings
          (by simpa only [result, Bool.false_eq_true, ↓reduceIte] using evaluated)⟩
    | true =>
      obtain ⟨value, evaluated⟩ := iht values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨Bool.toUInt64 (GuardNegation.denote negations flag),
        .booleanPropositionWord form negations guard yes no member hf meanings
          (by simpa only [result, ↓reduceIte] using evaluated)⟩
  | booleanChoiceWord form negations unequal left right yes no member present _ _ _ _ ihl ihr iht ihe =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨a, ha⟩ := ihl values typed
    obtain ⟨b, hb⟩ := ihr values typed
    obtain ⟨first, rfl⟩ := ha.booleanConversion_result
    obtain ⟨second, rfl⟩ := hb.booleanConversion_result
    cases result : booleanRelationDecision unequal first second with
    | false =>
      obtain ⟨value, evaluated⟩ := ihe values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨Bool.toUInt64 (GuardNegation.denote negations flag),
        .booleanChoiceWord form negations unequal left right yes no member hf ha hb
          (by simpa only [result, Bool.false_eq_true, ↓reduceIte] using evaluated)⟩
    | true =>
      obtain ⟨value, evaluated⟩ := iht values typed
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨Bool.toUInt64 (GuardNegation.denote negations flag),
        .booleanChoiceWord form negations unequal left right yes no member hf ha hb
          (by simpa only [result, ↓reduceIte] using evaluated)⟩
  | booleanEqualityWord form negations unequal left right member present _ _ ihl ihr =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨a, ha⟩ := ihl values typed
    obtain ⟨b, hb⟩ := ihr values typed
    obtain ⟨first, rfl⟩ := ha.booleanConversion_result
    obtain ⟨second, rfl⟩ := hb.booleanConversion_result
    exact ⟨Bool.toUInt64 (GuardNegation.denote negations (form.denote unequal first second)),
      .booleanEqualityWord form negations unequal left right member hf ha hb⟩
  | booleanBindingWord negations name form value body type member present _ _ ihv ihb =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨encoded, bound⟩ := ihv values typed
    obtain ⟨flag, rfl⟩ := bound.booleanConversion_result
    obtain ⟨result, evaluated⟩ := ihb (.boolean flag :: values) (by simp [Value.kind, typed])
    obtain ⟨outcome, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨Bool.toUInt64 (GuardNegation.denote negations outcome),
      .booleanBindingWord negations name form value body type member hf bound evaluated⟩
  | wordBindingBooleanWord negations name form value body type member present _ _ ihv ihb =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨flag, bound⟩ := ihv values typed
    obtain ⟨result, evaluated⟩ := ihb (.word flag :: values) (by simp [Value.kind, typed])
    obtain ⟨outcome, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨Bool.toUInt64 (GuardNegation.denote negations outcome),
      .wordBindingBooleanWord negations name form value body type member hf bound evaluated⟩
  | booleanWrappedWord negations wrapper body member present _ ih =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨encoded, evaluated⟩ := ih values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨Bool.toUInt64 (GuardNegation.denote negations (wrapper.denote flag)),
      .booleanWrappedWord negations wrapper body member hf evaluated⟩
  | booleanJunctionWord negations op left right member present _ _ ihl ihr =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨a, ha⟩ := ihl values typed
    obtain ⟨b, hb⟩ := ihr values typed
    obtain ⟨first, rfl⟩ := ha.booleanConversion_result
    obtain ⟨second, rfl⟩ := hb.booleanConversion_result
    exact ⟨Bool.toUInt64 (GuardNegation.denote negations (op.denote first second)),
      .booleanJunctionWord negations op left right member hf ha hb⟩
  | applyBooleanPredicateWord negations present _ ih =>
    obtain ⟨f, hf⟩ := booleanPredicateFunction_lookup typed present
    obtain ⟨argument, evaluated⟩ := ih values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨Bool.toUInt64 (GuardNegation.denote negations (f flag)),
      .applyBooleanPredicateWord negations hf evaluated⟩
  | apply present _ ih =>
    obtain ⟨f, hf⟩ := function_lookup typed present
    obtain ⟨x, hx⟩ := ih values typed
    exact ⟨f x, .apply hf hx⟩
  | letFn type _ _ ihf ihb =>
    have total := fun x => ihf (.word x :: values) (by simp [Value.kind, typed])
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.function false f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letFn type (fun x => (total x).choose_spec) hv⟩
  | letPredicateFn expression type _ _ ihf ihb =>
    have total : ∀ x, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.word x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := ihf (.word x :: values) (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.predicateFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letPredicateFn expression type (fun x => (total x).choose_spec) hv⟩
  | letBooleanPredicateFn expression type _ _ ihf ihb =>
    have total : ∀ x, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) expression.expr) (.boolean x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := ihf (.boolean x :: values) (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨value, hv⟩ := ihb (.booleanPredicateFunction f :: values) (by simp [Value.kind, typed])
    exact ⟨value, .letBooleanPredicateFn expression type (fun x => (total x).choose_spec) hv⟩
  | scopedSelection selected _ _ _ ihc iht ihe =>
    obtain ⟨condition, hc⟩ := ihc values typed
    obtain ⟨flag, rfl⟩ := hc.booleanConversion_result
    cases flag with
    | false =>
      obtain ⟨value, hv⟩ := ihe values typed
      obtain ⟨result, rfl⟩ := hv.booleanConversion_result
      exact ⟨result.toUInt64, .scopedSelection selected hc hv⟩
    | true =>
      obtain ⟨value, hv⟩ := iht values typed
      obtain ⟨result, rfl⟩ := hv.booleanConversion_result
      exact ⟨result.toUInt64, .scopedSelection selected hc hv⟩
  | scopedEquality related _ _ ihl ihr =>
    obtain ⟨left, hl⟩ := ihl values typed
    obtain ⟨a, rfl⟩ := hl.booleanConversion_result
    obtain ⟨right, hr⟩ := ihr values typed
    obtain ⟨b, rfl⟩ := hr.booleanConversion_result
    exact ⟨(related.relation.denote a b).toUInt64, .scopedEquality related hl hr⟩
  | scopedJunction joined _ _ ihl ihr =>
    obtain ⟨left, hl⟩ := ihl values typed
    obtain ⟨a, rfl⟩ := hl.booleanConversion_result
    obtain ⟨right, hr⟩ := ihr values typed
    obtain ⟨b, rfl⟩ := hr.booleanConversion_result
    exact ⟨(joined.operation.denote a b).toUInt64, .scopedJunction joined hl hr⟩
  | scopedNegation negated _ ih =>
    obtain ⟨value, evaluated⟩ := ih values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨(!flag).toUInt64, .scopedNegation negated evaluated⟩
  | scopedWrapper wrapped _ ih =>
    obtain ⟨value, evaluated⟩ := ih values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨(wrapped.wrapper.denote flag).toUInt64, .scopedWrapper wrapped evaluated⟩
  | scopedPredicate helper _ _ ihf ihb =>
    have total : ∀ x, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) helper.body.expr) (.word x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := ihf (.word x :: values) (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨encoded, evaluated⟩ := ihb (.predicateFunction f :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨flag.toUInt64, .scopedPredicate helper (fun x => (total x).choose_spec) evaluated⟩
  | scopedBooleanPredicate helper _ _ ihf ihb =>
    have total : ∀ x, ∃ flag : Bool,
        EvalWith (.app (.const ``Bool.toUInt64 []) helper.body.expr) (.boolean x :: values) flag.toUInt64 := by
      intro x
      obtain ⟨encoded, evaluated⟩ := ihf (.boolean x :: values) (by simp [Value.kind, typed])
      obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
      exact ⟨flag, evaluated⟩
    let f := fun x => (total x).choose
    obtain ⟨encoded, evaluated⟩ := ihb (.booleanPredicateFunction f :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    exact ⟨flag.toUInt64, .scopedBooleanPredicate helper (fun x => (total x).choose_spec) evaluated⟩
  | predicateInput input result _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .predicateInput input result evaluated⟩
  | booleanInput input result _ ih =>
    obtain ⟨outcome, evaluated⟩ := ih values typed
    exact ⟨outcome, .booleanInput input result evaluated⟩
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
