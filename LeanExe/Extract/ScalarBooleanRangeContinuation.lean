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

/-- Recognize local calls and exact Id forwarding under Boolean wrappers or metadata. -/
def booleanRangeWrappedCall? (boolean : Bool) (source : Lean.Expr) : Option (BooleanCall boolean × Lean.Expr) :=
  match source with
  | .app (.bvar 0) value => do
      let argument ← LeanExe.Source.ExprProofBinder.drop? 0 value
      pure (.direct, argument)
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam name domain (.app (.bvar 1) (.bvar 0)) binder) =>
      match boolean with
      | false => do
          let (input, output) ← booleanRangeBindTypes? input domain output
          let argument ← LeanExe.Source.ExprProofBinder.drop? 0 value
          pure (.forwardWord input output name binder, argument)
      | true => do
          let (input, output) ← booleanRangeFlagBindTypes? input domain output
          let argument ← LeanExe.Source.ExprProofBinder.drop? 0 value
          pure (.forwardBoolean input output name binder, argument)
  | .letE name type value (.bvar 0) nondep => do
      let type ← booleanType? type
      let (call, argument) ← booleanRangeWrappedCall? boolean value
      pure (.savedResult name type nondep call, argument)
  | source =>
      match _parsed : booleanRangeWrapper? source with
      | none => none
      | some (wrapper, body) => do
          let (call, argument) ← booleanRangeWrappedCall? boolean body
          pure (.wrapped wrapper call, argument)
termination_by sizeOf source
decreasing_by
  all_goals first | (simp_wf; omega) | exact booleanRangeWrapper_size _parsed

@[simp] theorem booleanRangeWrappedCall_direct (boolean : Bool) (argument : Lean.Expr) :
    booleanRangeWrappedCall? boolean ((BooleanCall.direct (boolean := boolean)).expr argument) = some (.direct, argument) := by
  simp [BooleanCall.expr, booleanRangeWrappedCall?]

theorem booleanRangeWrappedCall_wrapped (boolean : Bool) (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanRangeWrappedCall? boolean (wrapper.expr body) = (do
      let (call, argument) ← booleanRangeWrappedCall? boolean body
      pure (.wrapped wrapper call, argument)) := by
  have parsed := booleanRangeWrapper_accepts wrapper body
  cases wrapper <;> simp only [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure] at parsed ⊢
  all_goals rw [booleanRangeWrappedCall?.eq_def]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem booleanRangeWrappedCall_accepts (call : BooleanCall boolean) (argument : Lean.Expr) :
    booleanRangeWrappedCall? boolean (call.expr argument) = some (call, argument) := by
  induction call with
  | direct => exact booleanRangeWrappedCall_direct _ argument
  | wrapped wrapper inner ih =>
    rw [BooleanCall.expr, booleanRangeWrappedCall_wrapped]
    simp [ih]
  | savedResult name type nondep inner ih =>
    simp [BooleanCall.expr, booleanRangeWrappedCall?, ih]
  | forwardWord input output name binder =>
    simp [BooleanCall.expr, BooleanBindingForm.expr, booleanRangeWrappedCall?]
  | forwardBoolean input output name binder =>
    simp [BooleanCall.expr, BooleanBindingForm.expr, booleanRangeWrappedCall?]

theorem booleanRangeWrappedCall_sound {source : Lean.Expr} {call : BooleanCall boolean} {argument : Lean.Expr}
    (parsed : booleanRangeWrappedCall? boolean source = some (call, argument)) : source = call.expr argument := by
  induction source using (measure (fun e : Lean.Expr => sizeOf e)).wf.induction generalizing call argument with
  | h source ih =>
    rw [booleanRangeWrappedCall?.eq_def] at parsed
    split at parsed
    · rename_i value
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨actual, matched, rfl, rfl⟩ := parsed
      rw [LeanExe.Source.ExprProofBinder.drop_sound value 0 matched]
      rfl
    · rename_i input output value name domain binder
      cases boolean with
      | false =>
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨⟨inputType, outputType⟩, typed, actual, dropped, rfl, rfl⟩ := parsed
        obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound typed
        rw [LeanExe.Source.ExprProofBinder.drop_sound value 0 dropped]
        rfl
      | true =>
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨⟨inputType, outputType⟩, typed, actual, dropped, rfl, rfl⟩ := parsed
        obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound typed
        rw [LeanExe.Source.ExprProofBinder.drop_sound value 0 dropped]
        rfl
    · rename_i name type value nondep
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨output, typed, ⟨inner, actual⟩, found, rfl, rfl⟩ := parsed
      have smaller : sizeOf value < sizeOf (Lean.Expr.letE name type value (.bvar 0) nondep) := by simp; omega
      rw [booleanType_sound typed, ih value smaller found]
      rfl
    · split at parsed
      · contradiction
      · rename_i wrapper body matched
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨⟨inner, actual⟩, found, rfl, rfl⟩ := parsed
        rw [booleanRangeWrapper_sound matched, ih body (booleanRangeWrapper_size matched) found]
        rfl


def booleanRangeInput (boolean : Bool) (value : LeanExe.IR.Expr) : ScalarBinding :=
  if boolean then .boolean value else .word value

def booleanRangeArgument (boolean : Bool) (value : Lean.Expr) : Lean.Expr :=
  if boolean then .app (.const ``Bool.toUInt64 []) value else value

def booleanRangePredicate (locals : List ScalarBinding) (boolean : Bool)
    (expression : Lean.Expr) : ScalarBinding :=
  let function := fun argument => extractScalarExprWith (booleanRangeInput boolean argument :: locals)
    (.app (.const ``Bool.toUInt64 []) expression)
  if boolean then .booleanPredicateFunction function else .predicateFunction function

/-- Check a scalar helper before compiling its enclosing body. -/
def scalarBooleanRangePredicate (locals : List ScalarBinding) (boolean : Bool)
    (value : Lean.Expr) (body : ScalarBinding → Option ScalarRangeExitPlan) : Option ScalarRangeExitPlan := do
  let _ ← extractScalarExprWith (booleanRangeInput boolean (.u64 0) :: locals)
    (.app (.const ``Bool.toUInt64 []) value)
  body (booleanRangePredicate locals boolean value)

/-- Compile a direct application by binding its checked argument in the helper body. -/
def scalarBooleanRangeDirect (locals : List ScalarBinding) (boolean : Bool)
    (tail : Lean.Expr) (body : ScalarBinding → Option ScalarRangeExitPlan) : Option ScalarRangeExitPlan := do
  let (_, argument) ← booleanRangeWrappedCall? boolean tail
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
    (∃ (expression : Lean.Expr), ∃ checked, value = expression ∧
      extractScalarExprWith (booleanRangeInput boolean (.u64 0) :: locals)
        (.app (.const ``Bool.toUInt64 []) expression) = some checked ∧
      enclosing (booleanRangePredicate locals boolean expression) = some plan) ∨
    (∃ (call : BooleanCall boolean), ∃ argument bound, tail = call.expr argument ∧
      extractScalarExprWith locals (booleanRangeArgument boolean argument) = some bound ∧
      direct (booleanRangeInput boolean bound) = some plan) := by
  unfold scalarBooleanRangeContinuation at compiled
  cases first : scalarBooleanRangePredicate locals boolean value enclosing with
  | some result =>
    have same : result = plan := by simpa [first] using compiled
    subst result
    simp only [scalarBooleanRangePredicate, bind, Option.bind_eq_some_iff] at first
    obtain ⟨checked, validated, emitted⟩ := first
    exact .inl ⟨value, checked, rfl, validated, emitted⟩
  | none =>
    have second : scalarBooleanRangeDirect locals boolean tail direct = some plan := by
      simpa [first] using compiled
    simp only [scalarBooleanRangeDirect, bind, Option.bind_eq_some_iff] at second
    obtain ⟨⟨call, argument⟩, parsed, bound, validated, emitted⟩ := second
    exact .inr ⟨call, argument, bound, booleanRangeWrappedCall_sound parsed, validated, emitted⟩

theorem scalarBooleanRangeContinuation_accepts_scalar {locals : List ScalarBinding} {boolean : Bool}
    {expression : Lean.Expr} {tail : Lean.Expr}
    {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan} {checked : LeanExe.IR.Expr}
    {plan : ScalarRangeExitPlan}
    (validated : extractScalarExprWith (booleanRangeInput boolean (.u64 0) :: locals)
      (.app (.const ``Bool.toUInt64 []) expression) = some checked)
    (emitted : enclosing (booleanRangePredicate locals boolean expression) = some plan) :
    scalarBooleanRangeContinuation locals boolean expression tail enclosing direct = some plan := by
  simp [scalarBooleanRangeContinuation, scalarBooleanRangePredicate, validated, emitted]

theorem scalarBooleanRangeContinuation_accepts_direct {locals : List ScalarBinding} {boolean : Bool}
    {value argument : Lean.Expr} {call : BooleanCall boolean} {enclosing direct : ScalarBinding → Option ScalarRangeExitPlan}
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
