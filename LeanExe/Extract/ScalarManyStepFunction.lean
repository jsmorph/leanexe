import LeanExe.Extract.ScalarManyFunction
import LeanExe.Extract.ScalarStepSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar (ManyFunction FunctionSuffix Parameter)

/-- Larger helpers whose terminal annotation denotes a complete loop-step result. -/
abbrev scalarManyStepFunction? := manyFunction? scalarStepResultType?

@[simp] theorem scalarManyStepFunction_accepts (function : ManyFunction) :
    scalarManyStepFunction? (function.type LeanExe.Source.Scalar.Step.resultType) function.value = some function :=
  manyFunction_accepts _ _ scalarStepResultType_accepts
    (by intro annotation name rest bi; cases annotation <;> simp [LeanExe.Source.Scalar.Step.resultType]) function

theorem scalarManyStepFunction_sound {type value : Lean.Expr} {function : ManyFunction}
    (parsed : scalarManyStepFunction? type value = some function) :
    type = function.type LeanExe.Source.Scalar.Step.resultType ∧ value = function.value :=
  manyFunction_sound _ _ (fun _ _ => scalarStepResultType_sound) parsed

theorem scalarManyStepFunction_body_size {type value : Lean.Expr} {function : ManyFunction}
    (parsed : scalarManyStepFunction? type value = some function) :
    sizeOf function.body < sizeOf value := by
  rw [(scalarManyStepFunction_sound parsed).2]
  exact function.body_size

theorem scalarFunctionSuffix_rejects_step (suffix : FunctionSuffix) :
    scalarFunctionSuffix? (suffix.type LeanExe.Source.Scalar.Step.resultType) suffix.value = none := by
  induction suffix with
  | result annotation body =>
    cases annotation <;> simp [FunctionSuffix.type, FunctionSuffix.value, scalarFunctionSuffix?,
      functionSuffix?, LeanExe.Source.Scalar.Step.resultType, scalarResultType?, scalarResultType_not_step]
  | argument parameter rest ih =>
    simp [FunctionSuffix.type, FunctionSuffix.value, Parameter.arrow, Parameter.lambda,
      scalarFunctionSuffix?, functionSuffix?, ih]

theorem scalarManyFunction_rejects_step (function : ManyFunction) :
    scalarManyFunction? (function.type LeanExe.Source.Scalar.Step.resultType) function.value = none := by
  simp [scalarManyFunction?, manyFunction?, ManyFunction.type, ManyFunction.value,
    Parameter.arrow, Parameter.lambda, scalarFunctionSuffix_rejects_step]

end LeanExe.Extract.Core
