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
  | .letE name type value body nondep =>
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
                  | .forallE typeName input output typeBi, .lam paramName domain value paramBi =>
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
                                          | none =>
                                              match booleanRangeFlagBindTypes? input domain output with
                                              | some _ => do
                                                  let _ ← extractScalarExprWith (.boolean (.u64 0) :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value)
                                                  extractBooleanStepWith (.scalar (.booleanPredicateFunction (fun argument =>
                                                    extractScalarExprWith (.boolean argument :: locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) value))) :: locals) body
                                              | none =>
                                                  match _binary : booleanBinaryHelper? (.letE name
                                                      (.forallE typeName input output typeBi)
                                                      (.lam paramName domain value paramBi) body nondep) with
                                                  | none => none
                                                  | some helper => do
                                                      let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals.map BooleanStepBinding.toScalar)
                                                        (.app (.const ``Bool.toUInt64 []) helper.body)
                                                      let function := ScalarBinding.binaryPredicateFunction fun first second =>
                                                        extractScalarExprWith (.word second :: .word first :: locals.map BooleanStepBinding.toScalar)
                                                          (.app (.const ``Bool.toUInt64 []) helper.body)
                                                      extractBooleanStepWith (.scalar function :: locals) helper.continuation
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
  | .app (.app (.app (.app (.app (.const ``ForInStep.casesOn [.succ .zero, .zero]) (.const ``Bool []))
      (.lam _ (.app (.const ``ForInStep [.zero]) (.const ``Bool [])) type _)) value)
      (.lam _ (.const ``Bool []) doneBody _)) (.lam _ (.const ``Bool []) yieldBody _) => do
      let _ ← booleanStepResultType? type
      let result ← extractBooleanStepWith locals value
      let first ← extractBooleanStepWith (.scalar (.boolean result.value) :: locals) doneBody
      let second ← extractBooleanStepWith (.scalar (.boolean result.value) :: locals) yieldBody
      pure ⟨.ite (wordGuard result.done) first.value second.value,
        .ite (wordGuard result.done) first.done second.done⟩
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have bounds := booleanBinaryHelper_sizes _binary
      simp at bounds
      omega

theorem extractBooleanStepWith_letBinaryPredicate (locals : List BooleanStepBinding)
    (helper : BooleanBinaryHelper) :
    extractBooleanStepWith locals helper.expr = (do
      let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals.map BooleanStepBinding.toScalar)
        (.app (.const ``Bool.toUInt64 []) helper.body)
      let function := ScalarBinding.binaryPredicateFunction fun first second =>
        extractScalarExprWith (.word second :: .word first :: locals.map BooleanStepBinding.toScalar)
          (.app (.const ``Bool.toUInt64 []) helper.body)
      extractBooleanStepWith (.scalar function :: locals) helper.continuation) := by
  simp only [BooleanBinaryHelper.expr, BooleanBinaryFunctionBinding.expr, Parameter.arrow, Parameter.lambda]
  rw [extractBooleanStepWith]
  simp only [scalarResultType?, booleanType?, booleanStepResultType?,
    booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
    scalarBindTypes?, booleanRangeBindTypes?, booleanStepFlagWordTypes?, booleanRangeFlagBindTypes?,
    bind, Option.bind_some, Option.bind_none]
  change (match found : booleanBinaryHelper? helper.expr with
    | none => none
    | some value => do
        let _ ← extractScalarExprWith (.word (.u64 0) :: .word (.u64 0) :: locals.map BooleanStepBinding.toScalar)
          (.app (.const ``Bool.toUInt64 []) value.body)
        let function := ScalarBinding.binaryPredicateFunction fun first second =>
          extractScalarExprWith (.word second :: .word first :: locals.map BooleanStepBinding.toScalar)
            (.app (.const ``Bool.toUInt64 []) value.body)
        extractBooleanStepWith (.scalar function :: locals) value.continuation) = _
  split
  · rename_i found
    rw [booleanBinaryHelper_accepts] at found
    contradiction
  · rename_i actual found
    have equal := Option.some.inj ((booleanBinaryHelper_accepts helper).symm.trans found)
    subst actual
    rfl


end LeanExe.Extract.Core
set_option pp.maxSteps 100000 in
#check LeanExe.Extract.Core.extractBooleanStepWith.induct
