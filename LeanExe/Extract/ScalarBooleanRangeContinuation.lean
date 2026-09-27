import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarBooleanFunctionBinding
import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanCall

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Recover an argument that cannot refer to the local function itself. -/
def booleanRangeCallArgument? : Lean.Expr → Option Lean.Expr
  | .app (.bvar 0) argument => LeanExe.Source.ExprProofBinder.drop? 0 argument
  | _ => none

@[simp] theorem booleanRangeCallArgument_accepts (argument : Lean.Expr) :
    booleanRangeCallArgument? (.app (.bvar 0) (LeanExe.Source.ExprProofBinder.lift 0 argument)) =
      some argument := by
  simp [booleanRangeCallArgument?]

theorem booleanRangeCallArgument_sound {body argument : Lean.Expr}
    (parsed : booleanRangeCallArgument? body = some argument) :
    body = .app (.bvar 0) (LeanExe.Source.ExprProofBinder.lift 0 argument) := by
  unfold booleanRangeCallArgument? at parsed
  split at parsed
  · rename_i value
    rw [LeanExe.Source.ExprProofBinder.drop_sound value 0 parsed]
  · contradiction

/-- Recognize direct local calls under exact Boolean Id wrappers or metadata. -/
def booleanRangeWrappedCall? (source : Lean.Expr) : Option (BooleanCall × Lean.Expr) :=
  match source with
  | .app (.bvar 0) value => do
      let argument ← LeanExe.Source.ExprProofBinder.drop? 0 value
      pure (.direct, argument)
  | source =>
      match _parsed : booleanRangeWrapper? source with
      | none => none
      | some (wrapper, body) => do
          let (call, argument) ← booleanRangeWrappedCall? body
          pure (.wrapped wrapper call, argument)
termination_by sizeOf source
decreasing_by exact booleanRangeWrapper_size _parsed

@[simp] theorem booleanRangeWrappedCall_direct (argument : Lean.Expr) :
    booleanRangeWrappedCall? (BooleanCall.direct.expr argument) = some (.direct, argument) := by
  simp [BooleanCall.expr, booleanRangeWrappedCall?]

theorem booleanRangeWrappedCall_wrapped (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanRangeWrappedCall? (wrapper.expr body) = (do
      let (call, argument) ← booleanRangeWrappedCall? body
      pure (.wrapped wrapper call, argument)) := by
  have parsed := booleanRangeWrapper_accepts wrapper body
  cases wrapper <;> simp only [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure] at parsed ⊢
  all_goals rw [booleanRangeWrappedCall?.eq_def]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem booleanRangeWrappedCall_accepts (call : BooleanCall) (argument : Lean.Expr) :
    booleanRangeWrappedCall? (call.expr argument) = some (call, argument) := by
  induction call with
  | direct => exact booleanRangeWrappedCall_direct argument
  | wrapped wrapper inner ih =>
    rw [BooleanCall.expr, booleanRangeWrappedCall_wrapped]
    simp [ih]

theorem booleanRangeWrappedCall_sound {source : Lean.Expr} {call : BooleanCall} {argument : Lean.Expr}
    (parsed : booleanRangeWrappedCall? source = some (call, argument)) : source = call.expr argument := by
  fun_induction booleanRangeWrappedCall? source generalizing call argument with
  | case1 value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨actual, matched, rfl, rfl⟩ := parsed
    rw [LeanExe.Source.ExprProofBinder.drop_sound value 0 matched]
    rfl
  | case2 => contradiction
  | case3 source notDirect wrapper body matched ih =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨inner, actual⟩, found, rfl, rfl⟩ := parsed
    rw [booleanRangeWrapper_sound matched, ih found]
    rfl

def booleanRangeInput (boolean : Bool) (value : LeanExe.IR.Expr) : ScalarBinding :=
  if boolean then .boolean value else .word value

def booleanRangeArgument (boolean : Bool) (value : Lean.Expr) : Lean.Expr :=
  if boolean then .app (.const ``Bool.toUInt64 []) value else value

def booleanRangePredicate (locals : List ScalarBinding) (boolean : Bool)
    (expression : BooleanLocal) : ScalarBinding :=
  let function := fun argument => extractScalarExprWith (booleanRangeInput boolean argument :: locals)
    (.app (.const ``Bool.toUInt64 []) expression.expr)
  if boolean then .booleanPredicateFunction function else .predicateFunction function

/-- Check a scalar helper before compiling its enclosing body. -/
def scalarBooleanRangePredicate (locals : List ScalarBinding) (boolean : Bool)
    (value : Lean.Expr) (body : ScalarBinding → Option ScalarRangeExitPlan) : Option ScalarRangeExitPlan := do
  let expression ← booleanLocalOperands? value
  let _ ← extractScalarExprWith (booleanRangeInput boolean (.u64 0) :: locals)
    (.app (.const ``Bool.toUInt64 []) expression.expr)
  body (booleanRangePredicate locals boolean expression)

/-- Compile a direct application by binding its checked argument in the helper body. -/
def scalarBooleanRangeDirect (locals : List ScalarBinding) (boolean : Bool)
    (tail : Lean.Expr) (body : ScalarBinding → Option ScalarRangeExitPlan) : Option ScalarRangeExitPlan := do
  let (_, argument) ← booleanRangeWrappedCall? tail
  let bound ← extractScalarExprWith locals (booleanRangeArgument boolean argument)
  body (booleanRangeInput boolean bound)

/-- Preserve the existing scalar helper path before trying a loop continuation. -/
def scalarBooleanRangeContinuation (locals : List ScalarBinding) (boolean : Bool)
    (value tail : Lean.Expr) (enclosing direct : ScalarBinding → Option ScalarRangeExitPlan) :
    Option ScalarRangeExitPlan :=
  (scalarBooleanRangePredicate locals boolean value enclosing).orElse
    (fun _ => scalarBooleanRangeDirect locals boolean tail direct)

theorem scalarBooleanRangeContinuation_success {locals : List ScalarBinding} {boolean : Bool}
    {value tail : Lean.Expr} {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
    {plan : ScalarRangeExitPlan}
    (compiled : scalarBooleanRangeContinuation locals boolean value tail enclosing direct = some plan) :
    (∃ expression checked, value = expression.expr ∧
      extractScalarExprWith (booleanRangeInput boolean (.u64 0) :: locals)
        (.app (.const ``Bool.toUInt64 []) expression.expr) = some checked ∧
      enclosing (booleanRangePredicate locals boolean expression) = some plan) ∨
    (∃ (call : BooleanCall), ∃ argument bound, tail = call.expr argument ∧
      extractScalarExprWith locals (booleanRangeArgument boolean argument) = some bound ∧
      direct (booleanRangeInput boolean bound) = some plan) := by
  unfold scalarBooleanRangeContinuation at compiled
  cases first : scalarBooleanRangePredicate locals boolean value enclosing with
  | some result =>
    have same : result = plan := by simpa [first] using compiled
    subst result
    simp only [scalarBooleanRangePredicate, bind, Option.bind_eq_some_iff] at first
    obtain ⟨expression, parsed, checked, validated, emitted⟩ := first
    exact .inl ⟨expression, checked, booleanLocalOperands_sound parsed, validated, emitted⟩
  | none =>
    have second : scalarBooleanRangeDirect locals boolean tail direct = some plan := by
      simpa [first] using compiled
    simp only [scalarBooleanRangeDirect, bind, Option.bind_eq_some_iff] at second
    obtain ⟨⟨call, argument⟩, parsed, bound, validated, emitted⟩ := second
    exact .inr ⟨call, argument, bound, booleanRangeWrappedCall_sound parsed, validated, emitted⟩

theorem scalarBooleanRangeContinuation_accepts_scalar {locals : List ScalarBinding} {boolean : Bool}
    {expression : BooleanLocal} {tail : Lean.Expr}
    {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan} {checked : LeanExe.IR.Expr}
    {plan : ScalarRangeExitPlan}
    (validated : extractScalarExprWith (booleanRangeInput boolean (.u64 0) :: locals)
      (.app (.const ``Bool.toUInt64 []) expression.expr) = some checked)
    (emitted : enclosing (booleanRangePredicate locals boolean expression) = some plan) :
    scalarBooleanRangeContinuation locals boolean expression.expr tail enclosing direct = some plan := by
  simp [scalarBooleanRangeContinuation, scalarBooleanRangePredicate, validated, emitted]

theorem scalarBooleanRangeContinuation_accepts_direct {locals : List ScalarBinding} {boolean : Bool}
    {value argument : Lean.Expr} {call : BooleanCall} {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
    {bound : LeanExe.IR.Expr}
    (validated : extractScalarExprWith locals (booleanRangeArgument boolean argument) = some bound)
    (emitted : ∃ plan, direct (booleanRangeInput boolean bound) = some plan) :
    ∃ plan, scalarBooleanRangeContinuation locals boolean value
      (call.expr argument) enclosing direct = some plan := by
  unfold scalarBooleanRangeContinuation
  cases first : scalarBooleanRangePredicate locals boolean value enclosing with
  | some plan => exact ⟨plan, by simp⟩
  | none =>
    obtain ⟨plan, emitted⟩ := emitted
    exact ⟨plan, by simp [scalarBooleanRangeDirect, validated, emitted]⟩

end LeanExe.Extract.Core
