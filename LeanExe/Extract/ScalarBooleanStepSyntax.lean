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

@[simp] theorem scalarResultType_unitSyntax (form : UnitSyntax) : scalarResultType? form.type = none := by
  cases form <;> rfl

@[simp] theorem booleanType_unitSyntax (form : UnitSyntax) : booleanType? form.type = none := by
  cases form <;> rfl

@[simp] theorem booleanStepResultType_unitSyntax (form : UnitSyntax) : booleanStepResultType? form.type = none := by
  cases form <;> rfl

/-- Both sides of the leading unit binder retain the same concrete unit type. -/
def booleanStepUnitTypes? : Lean.Expr → Lean.Expr → Option UnitSyntax
  | .const ``Unit [], .const ``Unit [] => some .unit
  | .const ``PUnit [.succ .zero], .const ``PUnit [.succ .zero] => some .punit
  | _, _ => none

@[simp] theorem booleanStepUnitTypes_accepts (form : UnitSyntax) :
    booleanStepUnitTypes? form.type form.type = some form := by cases form <;> rfl

theorem booleanStepUnitTypes_sound {first second : Lean.Expr} {form : UnitSyntax}
    (parsed : booleanStepUnitTypes? first second = some form) :
    first = form.type ∧ second = form.type := by
  unfold booleanStepUnitTypes? at parsed
  split at parsed <;> cases parsed <;> exact ⟨rfl, rfl⟩

def booleanStepUnitValue? : Lean.Expr → Option UnitSyntax
  | .const ``Unit.unit [] => some .unit
  | .const ``PUnit.unit [.succ .zero] => some .punit
  | _ => none

@[simp] theorem booleanStepUnitValue_accepts (form : UnitSyntax) :
    booleanStepUnitValue? form.value = some form := by cases form <;> rfl

theorem booleanStepUnitValue_sound {source : Lean.Expr} {form : UnitSyntax}
    (parsed : booleanStepUnitValue? source = some form) : source = form.value := by
  unfold booleanStepUnitValue? at parsed
  split at parsed <;> cases parsed <;> rfl

/-- Exact declarations of Unit/PUnit-to-Bool-to-Boolean-step continuations. -/
def booleanUnitStepFunction? : Lean.Expr → Option BooleanStep.UnitBooleanFunction
  | .letE name (.forallE unitTypeName unitType (.forallE typeName input output typeBi) unitTypeBi)
      (.lam unitName unitDomain (.lam paramName domain body paramBi) unitBi) continuation nondep => do
      let unitForm ← booleanStepUnitTypes? unitType unitDomain
      let inputType ← booleanType? input
      let outputType ← booleanStepResultType? output
      if input = domain then
        some ⟨name, unitForm, unitTypeName, unitName, unitTypeBi, unitBi, inputType,
          outputType, typeName, paramName, typeBi, paramBi, body, continuation, nondep⟩
      else none
  | _ => none

@[simp] theorem booleanUnitStepFunction_accepts (helper : BooleanStep.UnitBooleanFunction) :
    booleanUnitStepFunction? helper.expr = some helper := by
  simp [BooleanStep.UnitBooleanFunction.expr, booleanUnitStepFunction?]

theorem booleanUnitStepFunction_sound {source : Lean.Expr} {helper : BooleanStep.UnitBooleanFunction}
    (parsed : booleanUnitStepFunction? source = some helper) : source = helper.expr := by
  unfold booleanUnitStepFunction? at parsed
  split at parsed
  · rename_i name unitTypeName unitType typeName input output typeBi unitTypeBi unitName unitDomain paramName domain body paramBi unitBi continuation nondep
    simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨unitForm, hu, inputType, hi, outputType, ho, accepted⟩ := parsed
    split at accepted
    · rename_i same
      cases accepted
      obtain ⟨rfl, rfl⟩ := booleanStepUnitTypes_sound hu
      obtain rfl := booleanType_sound hi
      obtain rfl := booleanStepResultType_sound ho
      subst domain
      rfl
    · contradiction
  · contradiction

theorem booleanUnitStepFunction_sizes {source : Lean.Expr} {helper : BooleanStep.UnitBooleanFunction}
    (parsed : booleanUnitStepFunction? source = some helper) :
    sizeOf helper.body < sizeOf source ∧ sizeOf helper.continuation < sizeOf source := by
  rw [booleanUnitStepFunction_sound parsed]
  exact ⟨helper.body_size, helper.continuation_size⟩

theorem booleanUnitStepFunction_not_binary (helper : BooleanStep.UnitBooleanFunction) :
    booleanBinaryHelper? helper.expr = none := by
  cases unit : helper.unitForm <;>
    simp only [BooleanStep.UnitBooleanFunction.expr, unit, UnitSyntax.type]
  all_goals unfold booleanBinaryHelper?; split <;> rfl

theorem booleanBinaryHelper_not_unitStep (helper : BooleanBinaryHelper) :
    booleanUnitStepFunction? helper.expr = none := by
  simp [booleanUnitStepFunction?, BooleanBinaryHelper.expr, BooleanBinaryFunctionBinding.expr,
    Parameter.arrow, Parameter.lambda, booleanStepUnitTypes?]

end LeanExe.Extract.Core
