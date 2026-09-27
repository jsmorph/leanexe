import LeanExe.Source.ScalarBooleanStep
import LeanExe.Extract.ScalarExpr
import LeanExe.Extract.ScalarBooleanStepBindings
import LeanExe.Extract.ScalarBooleanLetTypes
import LeanExe.Extract.ScalarBooleanRangeSyntax

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

@[simp] theorem scalarResultType_booleanStep (type : BooleanType) :
    scalarResultType? (BooleanStep.resultType type) = none := by
  induction type with
  | boolean => rfl
  | identity inner ih => simp [BooleanStep.resultType, scalarResultType?, ih]

@[simp] theorem booleanType_booleanStep (type : BooleanType) :
    booleanType? (BooleanStep.resultType type) = none := by
  induction type with
  | boolean => rfl
  | identity inner ih => simp [BooleanStep.resultType, booleanType?, ih]

def booleanStepResultBindTypes? (input domain output : Lean.Expr) : Option (BooleanType × BooleanType) := do
  let first ← booleanStepResultType? input
  let last ← booleanStepResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanStepResultBindTypes_accepts (input output : BooleanType) :
    booleanStepResultBindTypes? (BooleanStep.resultType input) (BooleanStep.resultType input)
      (BooleanStep.resultType output) = some (input, output) := by
  simp [booleanStepResultBindTypes?]

theorem booleanStepResultBindTypes_sound {input domain output : Lean.Expr}
    {first last : BooleanType}
    (parsed : booleanStepResultBindTypes? input domain output = some (first, last)) :
    input = BooleanStep.resultType first ∧ domain = BooleanStep.resultType first ∧ output = BooleanStep.resultType last := by
  simp only [booleanStepResultBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨booleanStepResultType_sound ha, same ▸ booleanStepResultType_sound ha, booleanStepResultType_sound hb⟩
  · contradiction

@[simp] theorem booleanStepWordBindTypes_not_step (input : BooleanType) (domain output : Lean.Expr) :
    booleanStepWordBindTypes? (BooleanStep.resultType input) domain output = none := by
  simp [booleanStepWordBindTypes?]

@[simp] theorem booleanStepFlagBindTypes_not_step (input : BooleanType) (domain output : Lean.Expr) :
    booleanStepFlagBindTypes? (BooleanStep.resultType input) domain output = none := by
  simp [booleanStepFlagBindTypes?]

@[simp] theorem booleanStepResultType_scalar (type : ResultType) :
    booleanStepResultType? type.expr = none := by
  induction type with
  | word => rfl
  | identity inner ih => simp [ResultType.expr, booleanStepResultType?, ih]

@[simp] theorem booleanStepResultType_boolean (type : BooleanType) :
    booleanStepResultType? type.expr = none := by
  induction type with
  | boolean => rfl
  | identity inner ih => simp [BooleanType.expr, booleanStepResultType?, ih]

/-- Exact domains and annotations of a Boolean-to-word local helper. -/
def booleanStepFlagWordTypes? (input domain output : Lean.Expr) : Option (BooleanType × ResultType) := do
  let first ← booleanType? input
  let last ← scalarResultType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanStepFlagWordTypes_accepts (input : BooleanType) (output : ResultType) :
    booleanStepFlagWordTypes? input.expr input.expr output.expr = some (input, output) := by
  simp [booleanStepFlagWordTypes?]

theorem booleanStepFlagWordTypes_sound {input domain output : Lean.Expr}
    {first : BooleanType} {last : ResultType}
    (parsed : booleanStepFlagWordTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = last.expr := by
  simp only [booleanStepFlagWordTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨booleanType_sound ha, same ▸ booleanType_sound ha, scalarResultType_sound hb⟩
  · contradiction

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
      | none =>
          match booleanType? type with
          | some _ => do
              let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
              extractBooleanStepWith (.scalar (.boolean result) :: locals) body
          | none =>
              match booleanStepResultType? type with
              | some _ => do
                  let result ← extractBooleanStepWith locals value
                  extractBooleanStepWith (.result result :: locals) body
              | none =>
                  match type, value with
                  | .forallE _ input output _, .lam _ domain value _ =>
                      match booleanStepWordBindTypes? input domain output with
                      | some _ => do
                          let _ ← extractBooleanStepWith (.scalar (.word (.u64 0)) :: locals) value
                          extractBooleanStepWith (.wordFunction (fun argument =>
                            extractBooleanStepWith (.scalar (.word argument) :: locals) value) :: locals) body
                      | none =>
                          match booleanStepFlagBindTypes? input domain output with
                          | some _ => do
                              let _ ← extractBooleanStepWith (.scalar (.boolean (.u64 0)) :: locals) value
                              extractBooleanStepWith (.booleanFunction (fun argument =>
                                extractBooleanStepWith (.scalar (.boolean argument) :: locals) value) :: locals) body
                          | none =>
                              match booleanStepResultBindTypes? input domain output with
                              | some _ => do
                                  let _ ← extractBooleanStepWith (.result ⟨.u64 0, .u64 0⟩ :: locals) value
                                  extractBooleanStepWith (.resultFunction (fun argument =>
                                    extractBooleanStepWith (.result argument :: locals) value) :: locals) body
                              | none =>
                                  match scalarBindTypes? input domain output with
                                  | some _ => do
                                      let _ ← extractScalarExprWith (.word (.u64 0) :: locals.map BooleanStepBinding.toScalar) value
                                      extractBooleanStepWith (.scalar (.function false (fun argument =>
                                        extractScalarExprWith (.word argument :: locals.map BooleanStepBinding.toScalar) value)) :: locals) body
                                  | none =>
                                      match booleanRangeBindTypes? input domain output with
                                      | some _ => do
                                          let _ ← extractScalarExprWith (.word (.u64 0) :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
                                          extractBooleanStepWith (.scalar (.predicateFunction (fun argument =>
                                            extractScalarExprWith (.word argument :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value))) :: locals) body
                                      | none =>
                                          match booleanStepFlagWordTypes? input domain output with
                                          | some _ => do
                                              let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals.map BooleanStepBinding.toScalar) value
                                              extractBooleanStepWith (.scalar (.booleanFunction (fun argument =>
                                                extractScalarExprWith (.boolean argument :: locals.map BooleanStepBinding.toScalar) value)) :: locals) body
                                          | none => do
                                              let _ ← booleanRangeFlagBindTypes? input domain output
                                              let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
                                              extractBooleanStepWith (.scalar (.booleanPredicateFunction (fun argument =>
                                                extractScalarExprWith (.boolean argument :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value))) :: locals) body
                  | _, _ => none
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value) (.lam _ domain body _) =>
      match booleanStepWordBindTypes? input domain output with
      | some _ => do
          let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) value
          extractBooleanStepWith (.scalar (.word result) :: locals) body
      | none =>
          match booleanStepFlagBindTypes? input domain output with
          | some _ => do
              let result ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
              extractBooleanStepWith (.scalar (.boolean result) :: locals) body
          | none => do
              let _ ← booleanStepResultBindTypes? input domain output
              let result ← extractBooleanStepWith locals value
              extractBooleanStepWith (.result result :: locals) body
  | .app (.bvar index) argument =>
      match locals[index]?.bind BooleanStepBinding.wordFunction? with
      | some f => do
          let value ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) argument
          f value
      | none =>
          match locals[index]?.bind BooleanStepBinding.booleanFunction? with
          | some f => do
              let value ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) argument)
              f value
          | none => do
              let f ← locals[index]?.bind BooleanStepBinding.resultFunction?
              let value ← extractBooleanStepWith locals argument
              f value
  | .bvar index => locals[index]?.bind BooleanStepBinding.result?
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
    rw [extractBooleanStepWith.eq_def] at compiled
    simp only [scalarResultType_accepts, bind,
      Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | letBoolean type value _ ih =>
    rw [extractBooleanStepWith.eq_def] at compiled
    simp only [scalarResultType_boolean, booleanType_accepts,
      bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | bindWord input output value _ ih =>
    simp only [BooleanStep.bindExpr, extractBooleanStepWith, booleanStepWordBindTypes_accepts,
      bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | bindBoolean input output value _ ih =>
    simp only [BooleanStep.bindExpr, extractBooleanStepWith, booleanStepWordBindTypes_not_boolean,
      booleanStepFlagBindTypes_accepts, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    exact ih emitted (bindings.cons (extractScalarExprWith_correct value matched bindings.toScalar))
  | letWordFunction input output function body ihf ihb =>
    simp only [BooleanStep.functionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes_accepts, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ihb emitted
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc (bindings.cons ha)
  | letBooleanFunction input output function body ihf ihb =>
    simp only [BooleanStep.functionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes_not_boolean, booleanStepFlagBindTypes_accepts,
      bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ihb emitted
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc (bindings.cons ha)
  | wordApply function argument =>
    rw [extractBooleanStepWith] at compiled
    split at compiled
    · rename_i f found
      simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨arg, matched, emitted⟩ := compiled
      exact bindings.wordFunction found function arg _ code
        (extractScalarExprWith_correct argument matched bindings.toScalar) emitted
    · simp [bindings.noBooleanFunction function, bindings.no_resultFunction_of_wordFunction function] at compiled
  | booleanApply function argument =>
    rw [extractBooleanStepWith, bindings.noWordFunction function] at compiled
    simp only at compiled
    split at compiled
    · rename_i f found
      simp only [bind, Option.bind_eq_some_iff] at compiled
      obtain ⟨arg, matched, emitted⟩ := compiled
      exact bindings.booleanFunction found function arg _ code
        (extractScalarExprWith_correct argument matched bindings.toScalar) emitted
    · simp [bindings.no_resultFunction_of_booleanFunction function] at compiled
  | resultVar present =>
    rw [extractBooleanStepWith] at compiled
    exact bindings.result compiled present
  | letResult type value body ihv ihb =>
    rw [extractBooleanStepWith.eq_def] at compiled
    simp only [scalarResultType_booleanStep, booleanType_booleanStep,
      booleanStepResultType_accepts, bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, emitted⟩ := compiled
    exact ihb emitted (bindings.cons (ihv matched bindings))
  | bindResult input output value body ihv ihb =>
    simp only [BooleanStep.bindExpr, extractBooleanStepWith, booleanStepWordBindTypes_not_step,
      booleanStepFlagBindTypes_not_step, booleanStepResultBindTypes_accepts,
      bind, Option.bind_some, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, emitted⟩ := compiled
    exact ihb emitted (bindings.cons (ihv matched bindings))
  | letResultFunction input output function body ihf ihb =>
    simp only [BooleanStep.functionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes_not_step, booleanStepFlagBindTypes_not_step, booleanStepResultBindTypes_accepts,
      bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ihb emitted
    apply bindings.cons
    intro argument value target ha hc
    exact ihf value hc (bindings.cons ha)
  | resultApply function argument ih =>
    rw [extractBooleanStepWith, bindings.no_wordFunction_of_resultFunction function,
      bindings.no_booleanFunction_of_resultFunction function] at compiled
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, found, arg, matched, emitted⟩ := compiled
    exact bindings.resultFunction (Option.bind_eq_some_iff.mpr found) function arg _ code
      (ih matched bindings) emitted
  | letScalarWordFunction input output function body ih =>
    simp only [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?,
      scalarResultType_accepts, booleanType_scalar,
      booleanStepResultType_scalar,
      bind, Option.bind_some, Option.bind_none, ite_eq_left, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)
  | letScalarPredicateFunction input output function body ih =>
    simp only [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?, booleanRangeBindTypes?,
      scalarResultType_accepts, booleanType_accepts, scalarResultType_boolean, booleanType_scalar,
      booleanStepResultType_scalar, booleanStepResultType_boolean,
      bind, Option.bind_some, Option.bind_none, ite_eq_left, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)
  | letScalarBooleanFunction input output function body ih =>
    simp only [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?, booleanRangeBindTypes?, booleanStepFlagWordTypes?,
      scalarResultType_accepts, booleanType_accepts, scalarResultType_boolean, booleanType_scalar,
      booleanStepResultType_scalar, booleanStepResultType_boolean,
      bind, Option.bind_some, Option.bind_none, ite_eq_left, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)
  | letScalarBooleanPredicateFunction input output function body ih =>
    simp only [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?, booleanRangeBindTypes?, booleanStepFlagWordTypes?, booleanRangeFlagBindTypes?,
      booleanType_accepts, scalarResultType_boolean,
      booleanStepResultType_boolean,
      bind, Option.bind_some, Option.bind_none, ite_eq_left, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    apply bindings.cons
    intro argument value target ha hc
    exact extractScalarExprWith_correct (function value) hc (bindings.toScalar.cons ha)

theorem extractBooleanStepWith_accepts {types : List BooleanStep.BindingKind} {source : Lean.Expr}
    (supported : BooleanStep.Supported types source) (locals : List BooleanStepBinding)
    (typed : locals.map BooleanStepBinding.kind = types) (total : ∀ binding ∈ locals, binding.Total) :
    ∃ code, extractBooleanStepWith locals source = some code := by
  have extend {locals : List BooleanStepBinding} {head : BooleanStepBinding}
      (tail : ∀ binding ∈ locals, binding.Total) (first : head.Total) :
      ∀ binding ∈ head :: locals, binding.Total := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact tail binding member
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
    exact ⟨code, by rw [extractBooleanStepWith.eq_def]; simp [scalarResultType_accepts, matched, emitted]⟩
  | letBoolean type value _ ih =>
    obtain ⟨result, matched⟩ := extractScalarExprWith_accepts value (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := ih (.scalar (.boolean result) :: locals) (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (by
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · trivial
      · exact total binding member)
    exact ⟨code, by rw [extractBooleanStepWith.eq_def]; simp [scalarResultType_boolean, matched, emitted]⟩
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
  | @letWordFunction types a b name typeName paramName typeBi paramBi nondep input output _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.scalar (.word argument) :: locals)
      (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractBooleanStepWith (.scalar (.word argument) :: locals) a
    obtain ⟨code, emitted⟩ := ihb (.wordFunction f :: locals)
      (by simp [BooleanStepBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.functionExpr, extractBooleanStepWith,
      scalarResultType?, booleanType?, booleanStepResultType?, hc, emitted, f]⟩
  | @letBooleanFunction types a b name typeName paramName typeBi paramBi nondep input output _ _ ihf ihb =>
    have accepts (argument : LeanExe.IR.Expr) := ihf (.scalar (.boolean argument) :: locals)
      (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (extend total trivial)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractBooleanStepWith (.scalar (.boolean argument) :: locals) a
    obtain ⟨code, emitted⟩ := ihb (.booleanFunction f :: locals)
      (by simp [BooleanStepBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.functionExpr, extractBooleanStepWith,
      scalarResultType?, booleanType?, booleanStepResultType?, hc, emitted, f]⟩
  | wordApply function argument =>
    obtain ⟨f, found⟩ := booleanStep_wordFunction_lookup (typed.symm ▸ function)
    obtain ⟨arg, matched⟩ := extractScalarExprWith_accepts argument (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := total _ (List.mem_of_getElem? found) arg
    exact ⟨code, by simp [extractBooleanStepWith, found, BooleanStepBinding.wordFunction?,
      matched, emitted]⟩
  | booleanApply function argument =>
    obtain ⟨f, found⟩ := booleanStep_booleanFunction_lookup (typed.symm ▸ function)
    obtain ⟨arg, matched⟩ := extractScalarExprWith_accepts argument (locals.map BooleanStepBinding.toScalar)
      (booleanStepBindings_typed typed) (booleanStepBindings_total total)
    obtain ⟨code, emitted⟩ := total _ (List.mem_of_getElem? found) arg
    exact ⟨code, by simp [extractBooleanStepWith, found, BooleanStepBinding.wordFunction?,
      BooleanStepBinding.booleanFunction?, matched, emitted]⟩
  | resultVar present =>
    obtain ⟨code, found⟩ := booleanStep_result_lookup (typed.symm ▸ present)
    exact ⟨code, by simp [extractBooleanStepWith, found, BooleanStepBinding.result?]⟩
  | letResult type _ _ ihv ihb =>
    obtain ⟨bound, matched⟩ := ihv locals typed total
    obtain ⟨code, emitted⟩ := ihb (.result bound :: locals)
      (by simp [BooleanStepBinding.kind, typed]) (extend total trivial)
    exact ⟨code, by rw [extractBooleanStepWith.eq_def]; simp [matched, emitted]⟩
  | bindResult input output _ _ ihv ihb =>
    obtain ⟨bound, matched⟩ := ihv locals typed total
    obtain ⟨code, emitted⟩ := ihb (.result bound :: locals)
      (by simp [BooleanStepBinding.kind, typed]) (extend total trivial)
    exact ⟨code, by simp [BooleanStep.bindExpr, extractBooleanStepWith, matched, emitted]⟩
  | @letResultFunction types a b name typeName paramName typeBi paramBi nondep input output _ _ ihf ihb =>
    have accepts (argument : ScalarStepCode) := ihf (.result argument :: locals)
      (by simp [BooleanStepBinding.kind, typed]) (extend total trivial)
    obtain ⟨checked, hc⟩ := accepts ⟨.u64 0, .u64 0⟩
    let f := fun argument => extractBooleanStepWith (.result argument :: locals) a
    obtain ⟨code, emitted⟩ := ihb (.resultFunction f :: locals)
      (by simp [BooleanStepBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.functionExpr, extractBooleanStepWith,
      scalarResultType?, booleanType?, booleanStepResultType?, hc, emitted, f]⟩
  | resultApply function argument ih =>
    obtain ⟨f, found⟩ := booleanStep_resultFunction_lookup (typed.symm ▸ function)
    obtain ⟨arg, matched⟩ := ih locals typed total
    obtain ⟨code, emitted⟩ := total _ (List.mem_of_getElem? found) arg
    exact ⟨code, by simp [extractBooleanStepWith, found, BooleanStepBinding.wordFunction?,
      BooleanStepBinding.booleanFunction?, BooleanStepBinding.resultFunction?, matched, emitted]⟩
  | @letScalarWordFunction a types b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.word argument :: locals.map BooleanStepBinding.toScalar)
      (by simp [ScalarBinding.kind, booleanStepBindings_typed typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact booleanStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals.map BooleanStepBinding.toScalar) a
    obtain ⟨code, emitted⟩ := ih (.scalar (.function false f) :: locals)
      (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?,
      scalarResultType_accepts, booleanType_scalar,
      booleanStepResultType_scalar,
      bind, Option.bind_some, Option.bind_none, hc, emitted, f]⟩
  | @letScalarPredicateFunction a types b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.word argument :: locals.map BooleanStepBinding.toScalar)
      (by simp [ScalarBinding.kind, booleanStepBindings_typed typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact booleanStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.word argument :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) a)
    obtain ⟨code, emitted⟩ := ih (.scalar (.predicateFunction f) :: locals)
      (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?, booleanRangeBindTypes?,
      scalarResultType_accepts, booleanType_accepts, scalarResultType_boolean, booleanType_scalar,
      booleanStepResultType_scalar, booleanStepResultType_boolean,
      bind, Option.bind_some, Option.bind_none, hc, emitted, f]⟩
  | @letScalarBooleanFunction a types b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.boolean argument :: locals.map BooleanStepBinding.toScalar)
      (by simp [ScalarBinding.kind, booleanStepBindings_typed typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact booleanStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals.map BooleanStepBinding.toScalar) a
    obtain ⟨code, emitted⟩ := ih (.scalar (.booleanFunction f) :: locals)
      (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?, booleanRangeBindTypes?, booleanStepFlagWordTypes?,
      scalarResultType_accepts, booleanType_accepts, scalarResultType_boolean, booleanType_scalar,
      booleanStepResultType_scalar, booleanStepResultType_boolean,
      bind, Option.bind_some, Option.bind_none, hc, emitted, f]⟩
  | @letScalarBooleanPredicateFunction a types b name typeName paramName typeBi paramBi nondep input output function body ih =>
    have accepts (argument : LeanExe.IR.Expr) := extractScalarExprWith_accepts function
      (.boolean argument :: locals.map BooleanStepBinding.toScalar)
      (by simp [ScalarBinding.kind, booleanStepBindings_typed typed]) (by
        intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · trivial
        · exact booleanStepBindings_total total binding member)
    obtain ⟨checked, hc⟩ := accepts (.u64 0)
    let f := fun argument => extractScalarExprWith (.boolean argument :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) a)
    obtain ⟨code, emitted⟩ := ih (.scalar (.booleanPredicateFunction f) :: locals)
      (by simp [BooleanStepBinding.kind, ScalarBinding.kind, typed]) (extend total accepts)
    exact ⟨code, by simp [BooleanStep.scalarFunctionExpr, extractBooleanStepWith, scalarResultType?, booleanType?, booleanStepResultType?,
      booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
      scalarBindTypes?, booleanRangeBindTypes?, booleanStepFlagWordTypes?, booleanRangeFlagBindTypes?,
      booleanType_accepts, scalarResultType_boolean,
      booleanStepResultType_boolean,
      bind, Option.bind_some, Option.bind_none, hc, emitted, f]⟩

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
  | case8 locals name type value body nondep notWord annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    rw [booleanType_sound typed]
    exact .letBoolean annotation (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case9 locals name type value body nondep notWord notFlag annotation parsed ihv ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, emitted⟩ := compiled
    rw [booleanStepResultType_sound parsed]
    exact .letResult annotation (ihv matched)
      (by simpa [BooleanStepBinding.kind] using ihb bound emitted)
  | case10 locals name body nondep typeName input output typeBi paramName domain value paramBi annotation parsed notWord notFlag notStep ih0 ihf ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepWordBindTypes_sound parsed
    exact .letWordFunction inputType outputType
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih0 matched)
      (by simpa [BooleanStepBinding.kind] using ihb emitted)
  | case11 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction annotation parsed notWord notFlag notStep ih0 ihf ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepFlagBindTypes_sound parsed
    exact .letBooleanFunction inputType outputType
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih0 matched)
      (by simpa [BooleanStepBinding.kind] using ihb emitted)
  | case12 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction annotation parsed notWord notFlag notStep ih0 ihf ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepResultBindTypes_sound parsed
    exact .letResultFunction inputType outputType
      (by simpa [BooleanStepBinding.kind] using ih0 matched)
      (by simpa [BooleanStepBinding.kind] using ihb emitted)
  | case13 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction annotation parsed notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := scalarBindTypes_sound parsed
    exact .letScalarWordFunction inputType outputType
      (by
        have supported := extractScalarExprWith_supported matched
        simp only [List.map_cons, List.map_map, Function.comp_def, BooleanStepBinding.toScalar_kind] at supported
        simpa only [ScalarBinding.kind, List.map_map, Function.comp_def] using supported)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih emitted)
  | case14 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction notScalarWord annotation parsed notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeBindTypes_sound parsed
    exact .letScalarPredicateFunction inputType outputType
      (by
        have supported := extractScalarExprWith_supported matched
        simp only [List.map_cons, List.map_map, Function.comp_def, BooleanStepBinding.toScalar_kind] at supported
        simpa only [ScalarBinding.kind, List.map_map, Function.comp_def] using supported)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih emitted)
  | case15 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction notScalarWord notScalarPredicate annotation parsed notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepFlagWordTypes_sound parsed
    exact .letScalarBooleanFunction inputType outputType
      (by
        have supported := extractScalarExprWith_supported matched
        simp only [List.map_cons, List.map_map, Function.comp_def, BooleanStepBinding.toScalar_kind] at supported
        simpa only [ScalarBinding.kind, List.map_map, Function.comp_def] using supported)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih emitted)
  | case16 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction notScalarWord notScalarPredicate notScalarBoolean notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨⟨inputType, outputType⟩, parsed, checked, matched, emitted⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound parsed
    exact .letScalarBooleanPredicateFunction inputType outputType
      (by
        have supported := extractScalarExprWith_supported matched
        simp only [List.map_cons, List.map_map, Function.comp_def, BooleanStepBinding.toScalar_kind] at supported
        simpa only [ScalarBinding.kind, List.map_map, Function.comp_def] using supported)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih emitted)
  | case17 => contradiction
  | case18 locals input output value name domain body bi annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepWordBindTypes_sound typed
    exact .bindWord inputType outputType (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case19 locals input output value name domain body bi notWord annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    obtain ⟨inputType, outputType⟩ := annotation
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepFlagBindTypes_sound typed
    exact .bindBoolean inputType outputType (expression matched)
      (by simpa [BooleanStepBinding.kind, ScalarBinding.kind] using ih result emitted)
  | case20 locals input output value name domain body bi notWord notFlag ihv ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨⟨inputType, outputType⟩, typed, bound, matched, emitted⟩ := compiled
    obtain ⟨rfl, rfl, rfl⟩ := booleanStepResultBindTypes_sound typed
    exact .bindResult inputType outputType (ihv matched)
      (by simpa [BooleanStepBinding.kind] using ihb bound emitted)
  | case21 locals index argument f found =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, matched, _⟩ := compiled
    exact .wordApply (booleanStep_wordFunction_kind found) (expression matched)
  | case22 locals index argument notWord f found =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, matched, _⟩ := compiled
    exact .booleanApply (booleanStep_booleanFunction_kind found) (expression matched)
  | case23 locals index argument notWord notFlag ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, found, arg, matched, _⟩ := compiled
    exact .resultApply (booleanStep_resultFunction_kind (Option.bind_eq_some_iff.mpr found)) (ih matched)
  | case24 locals index => exact .resultVar (booleanStep_result_kind compiled)
  | case25 => contradiction

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
  | case8 locals name type value body nondep notWord annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case9 locals name type value body nondep notWord notFlag annotation parsed ihv ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨bound, matched, emitted⟩ := compiled
    apply ihb bound emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv matched bindings
    · exact bindings binding member
  | case10 locals name body nondep typeName input output typeBi paramName domain value paramBi annotation parsed notWord notFlag notStep ih0 ihf ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ihb emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument code valid emitted
      apply ihf argument emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact bindings binding member
    · exact bindings binding member
  | case11 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction annotation parsed notWord notFlag notStep ih0 ihf ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ihb emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument code valid emitted
      apply ihf argument emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact bindings binding member
    · exact bindings binding member
  | case12 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction annotation parsed notWord notFlag notStep ih0 ihf ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ihb emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument code valid emitted
      apply ihf argument emitted
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact bindings binding member
    · exact bindings binding member
  | case13 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction annotation parsed notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target valid compiled
      apply extractScalarExprWith_invariant P literal binary choice compiled
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact booleanStepBindings_holds bindings binding member
    · exact bindings binding member
  | case14 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction notScalarWord annotation parsed notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target valid compiled
      apply extractScalarExprWith_invariant P literal binary choice compiled
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact booleanStepBindings_holds bindings binding member
    · exact bindings binding member
  | case15 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction notScalarWord notScalarPredicate annotation parsed notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨checked, _, emitted⟩ := compiled
    apply ih emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target valid compiled
      apply extractScalarExprWith_invariant P literal binary choice compiled
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact booleanStepBindings_holds bindings binding member
    · exact bindings binding member
  | case16 locals name body nondep typeName input output typeBi paramName domain value paramBi notWordFunction notFlagFunction notResultFunction notScalarWord notScalarPredicate notScalarBoolean notWord notFlag notStep ih =>
    simp only [List.attach_map_val] at ih
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, parsed, checked, _, emitted⟩ := compiled
    apply ih emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · intro argument target valid compiled
      apply extractScalarExprWith_invariant P literal binary choice compiled
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid
      · exact booleanStepBindings_holds bindings binding member
    · exact bindings binding member
  | case17 => contradiction
  | case18 locals input output value name domain body bi annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case19 locals input output value name domain body bi notWord annotation typed ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨result, matched, emitted⟩ := compiled
    apply ih result emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact expression matched bindings
    · exact bindings binding member
  | case20 locals input output value name domain body bi notWord notFlag ihv ihb =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨annotation, typed, bound, matched, emitted⟩ := compiled
    apply ihb bound emitted
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihv matched bindings
    · exact bindings binding member
  | case21 locals index argument f found =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, matched, emitted⟩ := compiled
    obtain ⟨binding, present, isFunction⟩ := Option.bind_eq_some_iff.mp found
    have same := BooleanStepBinding.wordFunction?_some.mp isFunction
    subst binding
    exact bindings _ (List.mem_of_getElem? present) arg code (expression matched bindings) emitted
  | case22 locals index argument notWord f found =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨arg, matched, emitted⟩ := compiled
    obtain ⟨binding, present, isFunction⟩ := Option.bind_eq_some_iff.mp found
    have same := BooleanStepBinding.booleanFunction?_some.mp isFunction
    subst binding
    exact bindings _ (List.mem_of_getElem? present) arg code (expression matched bindings) emitted
  | case23 locals index argument notWord notFlag ih =>
    simp only [bind, Option.bind_eq_some_iff] at compiled
    obtain ⟨f, found, arg, matched, emitted⟩ := compiled
    obtain ⟨binding, present, isFunction⟩ := found
    have same := BooleanStepBinding.resultFunction?_some.mp isFunction
    subst binding
    exact bindings _ (List.mem_of_getElem? present) arg code (ih matched bindings) emitted
  | case24 locals index =>
    obtain ⟨binding, found, matched⟩ := Option.bind_eq_some_iff.mp compiled
    have same := BooleanStepBinding.result?_some.mp matched
    subst binding
    exact bindings _ (List.mem_of_getElem? found)
  | case25 => contradiction

end LeanExe.Extract.Core
