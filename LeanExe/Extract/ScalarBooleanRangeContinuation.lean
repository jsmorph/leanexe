import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.ScalarBooleanFunctionBinding

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
  let argument ← booleanRangeCallArgument? tail
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
    (∃ argument bound, tail = .app (.bvar 0) (LeanExe.Source.ExprProofBinder.lift 0 argument) ∧
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
    obtain ⟨argument, parsed, bound, validated, emitted⟩ := second
    exact .inr ⟨argument, bound, booleanRangeCallArgument_sound parsed, validated, emitted⟩

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
    {value argument : Lean.Expr} {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
    {bound : LeanExe.IR.Expr}
    (validated : extractScalarExprWith locals (booleanRangeArgument boolean argument) = some bound)
    (emitted : ∃ plan, direct (booleanRangeInput boolean bound) = some plan) :
    ∃ plan, scalarBooleanRangeContinuation locals boolean value
      (.app (.bvar 0) (LeanExe.Source.ExprProofBinder.lift 0 argument)) enclosing direct = some plan := by
  unfold scalarBooleanRangeContinuation
  cases first : scalarBooleanRangePredicate locals boolean value enclosing with
  | some plan => exact ⟨plan, by simp⟩
  | none =>
    obtain ⟨plan, emitted⟩ := emitted
    exact ⟨plan, by simp [scalarBooleanRangeDirect, validated, emitted]⟩

end LeanExe.Extract.Core
