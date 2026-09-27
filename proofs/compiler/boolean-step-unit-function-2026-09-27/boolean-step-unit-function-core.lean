import LeanExe.Extract.ScalarBooleanStepSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

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
                                                  | none =>
                                                      match _unit : booleanUnitStepFunction? (.letE name
                                                          (.forallE typeName input output typeBi)
                                                          (.lam paramName domain value paramBi) body nondep) with
                                                      | none => none
                                                      | some helper => do
                                                          let _ ← extractBooleanStepWith
                                                            (.scalar (.boolean (.u64 0)) :: .scalar .unit :: locals) helper.body
                                                          let function := BooleanStepBinding.unitBooleanFunction helper.unitForm fun argument =>
                                                            extractBooleanStepWith (.scalar (.boolean argument) :: .scalar .unit :: locals) helper.body
                                                          extractBooleanStepWith (function :: locals) helper.continuation
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
  | .app (.app (.bvar index) unit) argument => do
      let unitForm ← booleanStepUnitValue? unit
      let f ← locals[index]?.bind (BooleanStepBinding.unitBooleanFunction? unitForm)
      let value ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) argument)
      f value
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
    | have bounds := booleanUnitStepFunction_sizes _unit
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

theorem extractBooleanStepWith_letUnitBooleanFunction (locals : List BooleanStepBinding)
    (helper : BooleanStep.UnitBooleanFunction) :
    extractBooleanStepWith locals helper.expr = (do
      let _ ← extractBooleanStepWith (.scalar (.boolean (.u64 0)) :: .scalar .unit :: locals) helper.body
      let function := BooleanStepBinding.unitBooleanFunction helper.unitForm fun argument =>
        extractBooleanStepWith (.scalar (.boolean argument) :: .scalar .unit :: locals) helper.body
      extractBooleanStepWith (function :: locals) helper.continuation) := by
  have noBinary := booleanUnitStepFunction_not_binary helper
  simp only [BooleanStep.UnitBooleanFunction.expr] at noBinary ⊢
  rw [extractBooleanStepWith]
  simp only [scalarResultType?, booleanType?, booleanStepResultType?,
    booleanStepWordBindTypes?, booleanStepFlagBindTypes?, booleanStepResultBindTypes?,
    scalarBindTypes?, booleanRangeBindTypes?, booleanStepFlagWordTypes?, booleanRangeFlagBindTypes?,
    scalarResultType_unitSyntax, booleanType_unitSyntax, booleanStepResultType_unitSyntax,
    bind, Option.bind_some, Option.bind_none, noBinary]
  split
  ·
    change (match found : booleanUnitStepFunction? helper.expr with
      | none => none
      | some value => do
          let _ ← extractBooleanStepWith (.scalar (.boolean (.u64 0)) :: .scalar .unit :: locals) value.body
          let function := BooleanStepBinding.unitBooleanFunction value.unitForm fun argument =>
            extractBooleanStepWith (.scalar (.boolean argument) :: .scalar .unit :: locals) value.body
          extractBooleanStepWith (function :: locals) value.continuation) = _
    split
    · rename_i found
      rw [booleanUnitStepFunction_accepts] at found
      contradiction
    · rename_i actual found
      have equal := Option.some.inj ((booleanUnitStepFunction_accepts helper).symm.trans found)
      subst actual
      rfl
  · rename_i actual found
    rw [noBinary] at found
    contradiction

theorem extractBooleanStepWith_unitBooleanApply (locals : List BooleanStepBinding)
    (unitForm : UnitSyntax) (index : Nat) (argument : Lean.Expr) :
    extractBooleanStepWith locals (.app (.app (.bvar index) unitForm.value) argument) = (do
      let f ← locals[index]?.bind (BooleanStepBinding.unitBooleanFunction? unitForm)
      let value ← extractScalarExprWith (locals.map BooleanStepBinding.toScalar) (.app (.const ``Bool.toUInt64 []) argument)
      f value) := by
  rw [extractBooleanStepWith, booleanStepUnitValue_accepts]
  rfl


end LeanExe.Extract.Core
set_option pp.maxSteps 100000 in
#check LeanExe.Extract.Core.extractBooleanStepWith.induct
