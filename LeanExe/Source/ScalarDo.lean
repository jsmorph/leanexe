import Lean

namespace LeanExe.Source.Scalar

/-- The two concrete result-type spellings used by pure scalar `do` blocks.
`Id UInt64` is definitionally UInt64, but remains explicit in elaborated syntax. -/
inductive ResultType where
  | word | identity
  deriving DecidableEq, Repr

def ResultType.expr : ResultType → Lean.Expr
  | .word => .const ``UInt64 []
  | .identity => .app (.const ``Id [.zero]) (.const ``UInt64 [])

namespace Identity

/-- Canonical standard Id operations, including their complete instance evidence. -/
def run (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``Id.run [.zero]) (.const ``UInt64 [])) body

def pure (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero])))) (.const ``UInt64 [])) body

def bind (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) (.const ``UInt64 [])) (.const ``UInt64 [])) value)
    (.lam name (.const ``UInt64 []) body bi)

end Identity
end LeanExe.Source.Scalar
