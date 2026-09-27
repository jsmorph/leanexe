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
    change (booleanStepResultType? inner).map BooleanType.identity = some type at parsed
    obtain ⟨found, matched, rfl⟩ := Option.map_eq_some_iff.mp parsed
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
  | metadata _ ih =>
    rw [extractBooleanStepWith] at compiled
    exact ih compiled bindings
  | @choose test evidence values flag yes no outcome type condition body ih =>
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

theorem extractBooleanStepWith_accepts {types : List BindingKind} {source : Lean.Expr}
    (supported : BooleanStep.Supported types source) (locals : List ScalarBinding)
    (typed : locals.map ScalarBinding.kind = types) (total : ∀ binding ∈ locals, binding.Total) :
    ∃ code, extractBooleanStepWith locals source = some code := by
  induction supported generalizing locals with
  | yieldDirect value =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value locals typed total
    exact ⟨⟨result, .u64 0⟩, by simp [BooleanStep.yieldDirect, extractBooleanStepWith, matched]⟩
  | doneDirect value =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value locals typed total
    exact ⟨⟨result, .u64 1⟩, by simp [BooleanStep.doneDirect, extractBooleanStepWith, matched]⟩
  | idRun type _ ih =>
    obtain ⟨code, emitted⟩ := ih locals typed total
    exact ⟨code, by simp [BooleanStep.idRun, extractBooleanStepWith, emitted]⟩
  | idPure type _ ih =>
    obtain ⟨code, emitted⟩ := ih locals typed total
    exact ⟨code, by simp [BooleanStep.idPure, extractBooleanStepWith, emitted]⟩
  | metadata _ ih =>
    obtain ⟨code, emitted⟩ := ih locals typed total
    exact ⟨code, by simp [extractBooleanStepWith, emitted]⟩
  | choose type condition _ _ yesIH noIH =>
    obtain ⟨guard, matched⟩ := extractScalarExprWith_accepts condition locals typed total
    obtain ⟨first, firstFound⟩ := yesIH locals typed total
    obtain ⟨second, secondFound⟩ := noIH locals typed total
    exact ⟨⟨.ite (wordGuard guard) first.value second.value, .ite (wordGuard guard) first.done second.done⟩,
      by simp [BooleanStep.choiceExpr, extractBooleanStepWith, matched, firstFound, secondFound]⟩
  | letWord type value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨code, emitted⟩ := ih (.word result :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by simp [extractBooleanStepWith, scalarResultType_accepts, matched, emitted]⟩
  | letBoolean type value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value locals typed total
    obtain ⟨code, emitted⟩ := ih (.boolean result :: locals) (by simp [ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by simp [extractBooleanStepWith, scalarResultType_boolean, matched, emitted]⟩

theorem extractBooleanStepWith_supported {locals : List ScalarBinding} {source : Lean.Expr}
    {code : ScalarStepCode} (compiled : extractBooleanStepWith locals source = some code) :
    BooleanStep.Supported (locals.map ScalarBinding.kind) source := by
  fun_induction extractBooleanStepWith locals source generalizing code with
  | case1 locals value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact .yieldDirect (extractScalarExprWith_supported matched)
  | case2 locals value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact .doneDirect (extractScalarExprWith_supported matched)
  | case3 locals type body ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, emitted⟩ := compiled
    rw [booleanStepResultType_sound typed]
    exact .idRun annotation (ih emitted)
  | case4 locals type body ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, emitted⟩ := compiled
    rw [booleanStepResultType_sound typed]
    exact .idPure annotation (ih emitted)
  | case5 locals data body ih => exact .metadata (ih compiled)
  | case6 locals type condition evidence yes no yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨annotation, typed, guard, matched, first, firstFound, second, secondFound, rfl⟩ := compiled
    rw [booleanStepResultType_sound typed]
    exact .choose annotation (extractScalarExprWith_supported matched) (yesIH firstFound) (noIH secondFound)
  | case7 locals name type value body nondep annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    rw [scalarResultType_sound typed]
    exact .letWord annotation (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih result emitted)
  | case8 locals name type value body nondep notWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, result, matched, emitted⟩ := compiled
    rw [booleanType_sound typed]
    exact .letBoolean annotation (extractScalarExprWith_supported matched)
      (by simpa [ScalarBinding.kind] using ih result emitted)
  | case9 => contradiction

theorem extractBooleanStepWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {locals : List ScalarBinding} {source : Lean.Expr} {code : ScalarStepCode}
    (compiled : extractBooleanStepWith locals source = some code)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : code.Holds P := by
  have expression {locals : List ScalarBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith locals source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled bindings
  fun_induction extractBooleanStepWith locals source generalizing code with
  | case1 locals value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact ⟨expression matched bindings, literal 0⟩
  | case2 locals value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact ⟨expression matched bindings, literal 1⟩
  | case3 locals type body ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, emitted⟩ := compiled
    exact ih emitted bindings
  | case4 locals type body ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, emitted⟩ := compiled
    exact ih emitted bindings
  | case5 locals data body ih => exact ih compiled bindings
  | case6 locals type condition evidence yes no yesIH noIH =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨annotation, typed, guard, matched, first, firstFound, second, secondFound, rfl⟩ := compiled
    obtain ⟨firstValue, firstDone⟩ := yesIH firstFound bindings
    obtain ⟨secondValue, secondDone⟩ := noIH secondFound bindings
    exact ⟨choice .eq guard (.u64 1) _ _ (expression matched bindings) (literal 1) firstValue secondValue,
      choice .eq guard (.u64 1) _ _ (expression matched bindings) (literal 1) firstDone secondDone⟩
  | case7 locals name type value body nondep annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case8 locals name type value body nondep notWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case9 => contradiction

end LeanExe.Extract.Core
