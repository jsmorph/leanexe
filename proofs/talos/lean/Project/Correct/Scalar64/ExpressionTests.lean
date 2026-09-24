import Project.Correct.Scalar64.Expression

namespace Project.Correct.Scalar64
open Project.ProofKit.ScalarTransition

example : (Expr.bin .divU (.const 99) (.const 0)).eval 0
    { params := [], locals := [.i64 0, .i64 0] } =
    some (0, { params := [], locals := [.i64 99, .i64 0] }) := rfl

example : (Expr.bin .remU (.const 99) (.const 0)).eval 0
    { params := [], locals := [.i64 0, .i64 0] } =
    some (99, { params := [], locals := [.i64 99, .i64 0] }) := rfl

example : (Expr.bin .shiftLeft (.const 3) (.const 65)).eval 0
    { params := [], locals := [] } = some (6, { params := [], locals := [] }) := rfl

#print axioms Expr.lower_spec
#print axioms Expr.eval_preserves_below

end Project.Correct.Scalar64
