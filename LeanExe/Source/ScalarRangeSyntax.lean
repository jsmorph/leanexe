import LeanExe.Source.ScalarDo
import LeanExe.Source.ScalarRange

namespace LeanExe.Source.Scalar.Range

/-- The canonical elaborated Nat literals used in unit-step range syntax. -/
def natLiteral (n : Nat) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
    (.app (.const ``instOfNatNat []) (.lit (.natVal n)))

/-- The standard Id range iterator, including its full instance evidence. -/
def head : Lean.Expr :=
  Lean.mkAppN (.const ``ForIn.forIn [.zero, .zero, .zero, .zero]) #[
    .const ``Id [.zero], .const ``Std.Legacy.Range [], .const ``Nat [],
    Lean.mkAppN (.const ``instForInOfForIn' [.zero, .zero, .zero, .zero]) #[
      .const ``Id [.zero], .const ``Std.Legacy.Range [], .const ``Nat [],
      Lean.mkAppN (.const ``inferInstance [.succ .zero]) #[
        Lean.mkAppN (.const ``Membership [.zero, .zero]) #[.const ``Nat [], .const ``Std.Legacy.Range []],
        .const ``Std.Legacy.instMembershipNatRange []],
      Lean.mkAppN (.const ``Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad [.zero, .zero])
        #[.const ``Id [.zero], .const ``Id.instMonad [.zero]]],
    .const ``UInt64 []]

def range (count : Lean.Expr) : Lean.Expr :=
  Lean.mkAppN (.const ``Std.Legacy.Range.mk []) #[natLiteral 0,
    .app (.const ``UInt64.toNat []) count, natLiteral 1, .const ``Nat.zero_lt_one []]

def call (count initial : Lean.Expr) (indexName accumulatorName : Lean.Name)
    (indexBi accumulatorBi : Lean.BinderInfo) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app head (range count)) initial)
    (.lam indexName (.const ``Nat []) (.lam accumulatorName (.const ``UInt64 []) body accumulatorBi) indexBi)

def yieldValue (value : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))))
    (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
    (.app (.app (.const ``ForInStep.yield [.zero]) (.const ``UInt64 [])) value)

/-- Yield-only step syntax and its scalar result expression. Local bindings
retain their type and order; the scalar grammar separately checks each binding
and body. Only the final standard yield is removed. -/
inductive YieldScalar : Lean.Expr → Lean.Expr → Prop where
  | yieldValue : YieldScalar (yieldValue value) value
  | letE (tail : YieldScalar body scalar) :
      YieldScalar (.letE name type value body nondep)
        (.letE name type value scalar nondep)
  | metadata (body : YieldScalar source scalar) :
      YieldScalar (.mdata data source) (.mdata data scalar)

end LeanExe.Source.Scalar.Range
