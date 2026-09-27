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
                      | none => do
                          let _ ← booleanStepFlagBindTypes? input domain output
                          let _ ← extractBooleanStepWith (.scalar (.boolean (.u64 0)) :: locals) value
                          extractBooleanStepWith (.booleanFunction (fun argument =>
                            extractBooleanStepWith (.scalar (.boolean argument) :: locals) value) :: locals) body
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
      | none => do
          let f ← locals[index]?.bind BooleanStepBinding.booleanFunction?
          let value ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) argument)
          f value
  | .bvar index => locals[index]?.bind BooleanStepBinding.result?
  | _ => none
termination_by source => sizeOf source
decreasing_by all_goals simp_wf; omega

example (locals : List BooleanStepBinding) (source : Lean.Expr) : True := by
  fun_induction extractBooleanStepWith locals source <;> trivial
#print extractBooleanStepWith.induct
end LeanExe.Extract.Core
