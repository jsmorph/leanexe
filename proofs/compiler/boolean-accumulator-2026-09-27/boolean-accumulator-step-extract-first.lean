import LeanExe.Source.ScalarBooleanStep
import LeanExe.Extract.ScalarExpr
import LeanExe.Extract.ScalarStepBindings
import LeanExe.Extract.ScalarBooleanLetTypes

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanStepResultType? : Lean.Expr → Option BooleanType
  | .app (.const ``ForInStep [.zero]) (.const ``Bool []) => some .boolean
  | .app (.const ``Id [.zero]) inner => BooleanType.identity <$> booleanStepResultType? inner
  | _ => none

@[simp] theorem booleanStepResultType_accepts (type : BooleanType) :
    booleanStepResultType? (BooleanStep.resultType type) = some type := by
  induction type with
  | boolean => rfl
  | identity inner ih => simp [BooleanStep.resultType, booleanStepResultType?, ih]

theorem booleanStepResultType_sound {source : Lean.Expr} {type : BooleanType}
    (parsed : booleanStepResultType? source = some type) : source = BooleanStep.resultType type := by
  fun_induction booleanStepResultType? source generalizing type with
  | case1 => cases parsed; rfl
  | case2 inner ih =>
    simp only [Option.map_eq_some_iff] at parsed
    obtain ⟨found, matched, rfl⟩ := parsed
    simp [BooleanStep.resultType, ih matched]
  | case3 => contradiction

/-- Compile a Boolean update and its exit flag as two read-only word expressions. -/
def extractBooleanStepWith (locals : List ScalarBinding) : Lean.Expr → Option ScalarStepCode
  | .app (.app (.const ``ForInStep.yield [.zero]) (.const ``Bool [])) value => do
      let result ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
      pure ⟨result, .u64 0⟩
  | .app (.app (.const ``ForInStep.done [.zero]) (.const ``Bool [])) value => do
      let result ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
      pure ⟨result, .u64 1⟩
  | .app (.app (.const ``Id.run [.zero]) type) body => do
      let _ ← booleanStepResultType? type
      extractBooleanStepWith locals body
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) type) body => do
      let _ ← booleanStepResultType? type
      extractBooleanStepWith locals body
  | .mdata _ body => extractBooleanStepWith locals body
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no => do
      let _ ← booleanStepResultType? type
      let condition ← extractScalarExprWith locals (BooleanStep.decision condition evidence)
      let first ← extractBooleanStepWith locals yes
      let second ← extractBooleanStepWith locals no
      pure ⟨.ite (wordGuard condition) first.value second.value,
        .ite (wordGuard condition) first.done second.done⟩
  | .letE _ type value body _ =>
      match scalarResultType? type with
      | some _ => do
          let result ← extractScalarExprWith locals value
          extractBooleanStepWith (.word result :: locals) body
      | none => do
          let _ ← booleanType? type
          let result ← extractScalarExprWith locals (.app (.const ``Bool.toUInt64 []) value)
          extractBooleanStepWith (.boolean result :: locals) body
  | _ => none
termination_by source => sizeOf source
decreasing_by all_goals simp_wf; omega

theorem extractBooleanStepWith_correct {source : Lean.Expr} {values : List Value}
    {outcome : ForInStep Bool} (semantics : BooleanStep.Eval source values outcome)
    {locals : List ScalarBinding} {code : ScalarStepCode} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanStepWith locals source = some code)
    (bindings : ScalarBindingsMatch locals values store) :
    code.Meaning store (BooleanAccumulator.encodeStep outcome) := by
  induction semantics generalizing locals code with
  | yieldDirect value =>
    simp only [BooleanStep.yieldDirect, extractBooleanStepWith, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value matched bindings, .const⟩
  | doneDirect value =>
    simp only [BooleanStep.doneDirect, extractBooleanStepWith, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value matched bindings, .const⟩
  | idRun type _ ih =>
    simp only [BooleanStep.idRun, extractBooleanStepWith, booleanStepResultType_accepts,
      bind, Option.bind_some] at compiled
    exact ih compiled bindings
  | idPure type _ ih =>
    simp only [BooleanStep.idPure, extractBooleanStepWith, booleanStepResultType_accepts,
      bind, Option.bind_some] at compiled
    exact ih compiled bindings
  | metadata _ ih => exact ih compiled bindings
  | @choose type test evidence values flag yes no outcome condition body ih =>
    simp only [BooleanStep.choiceExpr, extractBooleanStepWith, booleanStepResultType_accepts,
      bind, pure, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, matched, first, firstFound, second, secondFound, rfl⟩ := compiled
    have test := wordGuard_correct (extractScalarExprWith_correct condition matched bindings)
    cases flag with
    | false =>
      obtain ⟨valueEval, doneEval⟩ := ih secondFound bindings
      exact ⟨.iteFalse test valueEval, .iteFalse test doneEval⟩
    | true =>
      obtain ⟨valueEval, doneEval⟩ := ih firstFound bindings
      exact ⟨.iteTrue test valueEval, .iteTrue test doneEval⟩
  | letWord type value _ ih =>
    simp only [extractBooleanStepWith, scalarResultType_accepts, bind,
      Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings))
  | letBoolean type value _ ih =>
    simp only [extractBooleanStepWith, scalarResultType_boolean, booleanType_accepts,
      bind, Option.bind_some, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings))

end LeanExe.Extract.Core
