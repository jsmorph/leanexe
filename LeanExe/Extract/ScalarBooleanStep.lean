import LeanExe.Source.ScalarBooleanStep
import LeanExe.Extract.ScalarExpr
import LeanExe.Extract.ScalarBooleanStepBindings
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

/-- A standard word-to-Boolean-step bind preserves its exact continuation domain. -/
def booleanStepWordBindTypes? (input domain output : Lean.Expr) : Option (ResultType × BooleanType) := do
  let first ← scalarResultType? input
  let last ← booleanStepResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanStepWordBindTypes_accepts (input : ResultType) (output : BooleanType) :
    booleanStepWordBindTypes? input.expr input.expr (BooleanStep.resultType output) = some (input, output) := by
  simp [booleanStepWordBindTypes?]

theorem booleanStepWordBindTypes_sound {input domain output : Lean.Expr}
    {first : ResultType} {last : BooleanType}
    (parsed : booleanStepWordBindTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = BooleanStep.resultType last := by
  simp only [booleanStepWordBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨scalarResultType_sound ha, same ▸ scalarResultType_sound ha, booleanStepResultType_sound hb⟩
  · contradiction

/-- A standard Boolean-to-Boolean-step bind preserves its exact continuation domain. -/
def booleanStepFlagBindTypes? (input domain output : Lean.Expr) : Option (BooleanType × BooleanType) := do
  let first ← booleanType? input
  let last ← booleanStepResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanStepFlagBindTypes_accepts (input : BooleanType) (output : BooleanType) :
    booleanStepFlagBindTypes? input.expr input.expr (BooleanStep.resultType output) = some (input, output) := by
  simp [booleanStepFlagBindTypes?]

theorem booleanStepFlagBindTypes_sound {input domain output : Lean.Expr}
    {first : BooleanType} {last : BooleanType}
    (parsed : booleanStepFlagBindTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = BooleanStep.resultType last := by
  simp only [booleanStepFlagBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨booleanType_sound ha, same ▸ booleanType_sound ha, booleanStepResultType_sound hb⟩
  · contradiction

@[simp] theorem booleanStepWordBindTypes_not_boolean (input : BooleanType) (domain output : Lean.Expr) :
    booleanStepWordBindTypes? input.expr domain output = none := by
  simp [booleanStepWordBindTypes?, scalarResultType_boolean]

/-- Compile a Boolean update and its exit flag as two read-only word expressions. -/
def extractBooleanStepWith (locals : List BooleanStepBinding) : Lean.Expr → Option ScalarStepCode
  | .app (.app (.const ``ForInStep.yield [.zero]) (.const ``Bool [])) value => do
      let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
      pure ⟨result, .u64 0⟩
  | .app (.app (.const ``ForInStep.done [.zero]) (.const ``Bool [])) value => do
      let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
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
      let condition ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (BooleanStep.decision condition evidence)
      let first ← extractBooleanStepWith locals yes
      let second ← extractBooleanStepWith locals no
      pure ⟨.ite (wordGuard condition) first.value second.value,
        .ite (wordGuard condition) first.done second.done⟩
  | .letE _ type value body _ =>
      match scalarResultType? type with
      | some _ => do
          let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) value
          extractBooleanStepWith (.scalar (.word result) :: locals) body
      | none => do
          let _ ← booleanType? type
          let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
          extractBooleanStepWith (.scalar (.boolean result) :: locals) body
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value) (.lam _ domain body _) =>
      match booleanStepWordBindTypes? input domain output with
      | some _ => do
          let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) value
          extractBooleanStepWith (.scalar (.word result) :: locals) body
      | none => do
          let _ ← booleanStepFlagBindTypes? input domain output
          let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
          extractBooleanStepWith (.scalar (.boolean result) :: locals) body
  | _ => none
termination_by source => sizeOf source
decreasing_by all_goals simp_wf; omega

theorem extractBooleanStepWith_correct {source : Lean.Expr} {values : List BooleanStep.Value}
    {outcome : ForInStep Bool} (semantics : BooleanStep.Eval source values outcome)
    {locals : List BooleanStepBinding} {code : ScalarStepCode} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanStepWith locals source = some code)
    (bindings : BooleanStepBindingsMatch locals values store) :
    code.Meaning store (BooleanAccumulator.encodeStep outcome) := by
  induction semantics generalizing locals code with
  | yieldDirect value =>
    simp only [BooleanStep.yieldDirect, extractBooleanStepWith, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value matched bindings.toScalar, .const⟩
  | doneDirect value =>
    simp only [BooleanStep.doneDirect, extractBooleanStepWith, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact ⟨extractScalarExprWith_correct value matched bindings.toScalar, .const⟩
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
  | @choose test evidence flag yes no values outcome type condition body ih =>
    simp only [BooleanStep.choiceExpr, extractBooleanStepWith, booleanStepResultType_accepts,
      bind, pure, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨guard, matched, first, firstFound, second, secondFound, rfl⟩ := compiled
    have test := wordGuard_correct (extractScalarExprWith_correct condition matched bindings.toScalar)
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
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | letBoolean type value _ ih =>
    simp only [extractBooleanStepWith, scalarResultType_boolean, booleanType_accepts,
      bind, Option.bind_some, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | bindWord input output value _ ih =>
    simp only [BooleanStep.bindExpr, extractBooleanStepWith, booleanStepWordBindTypes_accepts,
      bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | bindBoolean input output value _ ih =>
    simp only [BooleanStep.bindExpr, extractBooleanStepWith, booleanStepWordBindTypes_not_boolean,
      booleanStepFlagBindTypes_accepts, bind, Option.bind_some, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))

theorem extractBooleanStepWith_accepts {types : List BooleanStep.BindingKind} {source : Lean.Expr}
    (supported : BooleanStep.Supported types source) (locals : List BooleanStepBinding)
    (typed : locals.map BooleanStepBinding.kind = types) (total : ∀ binding ∈ locals, binding.Total) :
    ∃ code, extractBooleanStepWith locals source = some code := by
  induction supported generalizing locals with
  | yieldDirect value =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    exact ⟨⟨result, .u64 0⟩, by simp [BooleanStep.yieldDirect, extractBooleanStepWith, matched]⟩
  | doneDirect value =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
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
    obtain ⟨guard, matched⟩ := extractScalarExprWith_accepts condition (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨first, firstFound⟩ := yesIH locals typed total
    obtain ⟨second, secondFound⟩ := noIH locals typed total
    exact ⟨⟨.ite (wordGuard guard) first.value second.value, .ite (wordGuard guard) first.done second.done⟩,
      by simp [BooleanStep.choiceExpr, extractBooleanStepWith, matched, firstFound, secondFound]⟩
  | letWord type value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := ih (.scalar (.word result) :: locals) (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by simp [extractBooleanStepWith, scalarResultType_accepts, matched, emitted]⟩
  | letBoolean type value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := ih (.scalar (.boolean result) :: locals) (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by simp [extractBooleanStepWith, scalarResultType_boolean, matched, emitted]⟩
  | bindWord input output value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := ih (.scalar (.word result) :: locals) (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by simp [BooleanStep.bindExpr, extractBooleanStepWith, matched, emitted]⟩
  | bindBoolean input output value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := ih (.scalar (.boolean result) :: locals) (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by simp [BooleanStep.bindExpr, extractBooleanStepWith, matched, emitted]⟩

theorem extractBooleanStepWith_supported {locals : List BooleanStepBinding} {source : Lean.Expr}
    {code : ScalarStepCode} (compiled : extractBooleanStepWith locals source = some code) :
    BooleanStep.Supported (locals.map BooleanStepBinding.kind) source := by
  have expression {locals : List BooleanStepBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith (locals.map BooleanStepBinding.toScalar) source = some target) :
      SupportedWith ((locals.map BooleanStepBinding.kind).map BooleanStep.BindingKind.toScalar) source := by
    simpa [List.map_map, Function.comp_def] using extractScalarExprWith_supported compiled
  fun_induction extractBooleanStepWith locals source generalizing code with
  | case1 locals value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact .yieldDirect (expression matched)
  | case2 locals value =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨result, matched, rfl⟩ := compiled
    exact .doneDirect (expression matched)
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
    exact .choose annotation (expression matched) (yesIH firstFound) (noIH secondFound)
  | case7 locals name type value body nondep annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    rw [scalarResultType_sound typed]
    exact .letWord annotation (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case8 locals name type value body nondep notWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, result, matched, emitted⟩ := compiled
    rw [booleanType_sound typed]
    exact .letBoolean annotation (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case9 locals input output value name domain body bi annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepWordBindTypes_sound typed
    exact .bindWord inputType outputType (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case10 locals input output value name domain body bi notWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨⟨inputType, outputType⟩, typed, result, matched, emitted⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepFlagBindTypes_sound typed
    exact .bindBoolean inputType outputType (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case11 => contradiction

theorem extractBooleanStepWith_invariant (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {locals : List BooleanStepBinding} {source : Lean.Expr} {code : ScalarStepCode}
    (compiled : extractBooleanStepWith locals source = some code)
    (bindings : ∀ binding ∈ locals, binding.Holds P) : code.Holds P := by
  have expression {locals : List BooleanStepBinding} {source : Lean.Expr} {target : LeanExe.IR.Expr}
      (compiled : extractScalarExprWith (locals.map BooleanStepBinding.toScalar) source = some target)
      (bindings : ∀ binding ∈ locals, binding.Holds P) : P target :=
    extractScalarExprWith_invariant P literal binary choice compiled (booleanStepBindings_holds bindings)
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
  | case9 locals input output value name domain body bi annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case10 locals input output value name domain body bi notWord ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case11 => contradiction

end LeanExe.Extract.Core
