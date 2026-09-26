import LeanExe.Extract.ScalarBooleanType
import LeanExe.Extract.ScalarDo

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem scalarResultType_boolean (type : BooleanType) :
    scalarResultType? type.expr = none := by
  induction type with
  | boolean => rfl
  | identity inner ih => simp [BooleanType.expr, scalarResultType?, ih]

@[simp] theorem booleanType_scalar (type : ResultType) :
    booleanType? type.expr = none := by
  induction type with
  | word => rfl
  | identity inner ih => simp [ResultType.expr, booleanType?, ih]

end LeanExe.Extract.Core
