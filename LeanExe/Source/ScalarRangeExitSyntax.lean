import LeanExe.Source.ScalarRangeStrideSyntax

namespace LeanExe.Source.Scalar.Range.Exit

/-- Range index types may carry Lean metadata, which has no effect on their
Nat meaning. The exact annotation is retained in source syntax. -/
structure IndexType where
  expr : Lean.Expr
  isNat : expr.consumeMData = .const ``Nat []

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
    .const ``UInt64 []]


def call (indexType : IndexType) (stride : Stride) (first : Count) (count : Count) (initial : Lean.Expr) (indexName accumulatorName : Lean.Name)
    (indexBi accumulatorBi : Lean.BinderInfo) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (head indexType.expr) (count.range first stride.number stride.evidence)) initial)
    (.lam indexName indexType.expr (.lam accumulatorName (.const ``UInt64 []) body accumulatorBi) indexBi)

end LeanExe.Source.Scalar.Range.Exit
