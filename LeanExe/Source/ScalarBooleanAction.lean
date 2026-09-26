import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- Boolean actions share the recursive value syntax, including Id and metadata. -/
inductive BooleanAction where
  | value (expression : BooleanLocal)

namespace BooleanAction

def leaf : BooleanAction → BooleanLocal
  | .value expression => expression

def expr (action : BooleanAction) : Lean.Expr := action.leaf.expr

def pure (body : BooleanAction) (type : BooleanType := .boolean) : BooleanAction :=
  .value (.wrapped 0 (.pure type) body.leaf)

def run (body : BooleanAction) (type : BooleanType := .boolean) : BooleanAction :=
  .value (.wrapped 0 (.run type) body.leaf)

def metadata (data : Lean.MData) (body : BooleanAction) : BooleanAction :=
  .value (.wrapped 0 (.metadata data) body.leaf)

theorem operands_size (action : BooleanAction) {operand : Lean.Expr}
    (member : operand ∈ action.leaf.operands) : sizeOf operand < sizeOf action.expr :=
  action.leaf.operands_size member

end BooleanAction
end LeanExe.Source.Scalar
