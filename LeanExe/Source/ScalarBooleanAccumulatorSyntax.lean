import LeanExe.Source.ScalarRangeExitSyntax
import LeanExe.Source.ScalarBooleanIteration

namespace LeanExe.Source.Scalar.BooleanAccumulator

abbrev IndexType := Range.Exit.IndexType
abbrev Stride := Range.Exit.Stride
abbrev Count := Range.Exit.Count

def head (indexType : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const ``ForIn.forIn [.zero, .zero, .zero, .zero]) #[
    .const ``Id [.zero], .const ``Std.Legacy.Range [], indexType,
    Lean.mkAppN (.const ``instForInOfForIn' [.zero, .zero, .zero, .zero]) #[
      .const ``Id [.zero], .const ``Std.Legacy.Range [], .const ``Nat [],
      Lean.mkAppN (.const ``inferInstance [.succ .zero]) #[
        Lean.mkAppN (.const ``Membership [.zero, .zero]) #[.const ``Nat [], .const ``Std.Legacy.Range []],
        .const ``Std.Legacy.instMembershipNatRange []],
      Lean.mkAppN (.const ``Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad [.zero, .zero])
        #[.const ``Id [.zero], .const ``Id.instMonad [.zero]]],
    .const ``Bool []]


def call (indexType : IndexType) (stride : Stride) (first : Count) (count : Count) (initial : Lean.Expr) (indexName accumulatorName : Lean.Name)
    (indexBi accumulatorBi : Lean.BinderInfo) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (head indexType.expr) (count.range first stride.number stride.evidence)) initial)
    (.lam indexName indexType.expr (.lam accumulatorName (.const ``Bool []) body accumulatorBi) indexBi)

end LeanExe.Source.Scalar.BooleanAccumulator
