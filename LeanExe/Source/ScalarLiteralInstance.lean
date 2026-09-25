import Lean

namespace LeanExe.Source.Scalar

/-- A constant standard UInt64 numeral instance, possibly under unused binders.
The index counts arguments still required before reaching the instance. The only
value leaf is the exact standard instance for `number`; no local or custom
instance can be a leaf. Lets and application arguments cannot affect that leaf. -/
inductive LiteralInstance (number : Nat) : Nat → Lean.Expr → Prop where
  | standard : LiteralInstance number 0
      (.app (.const ``UInt64.instOfNat []) (.lit (.natVal number)))
  | lambda (body : LiteralInstance number arity expression) :
      LiteralInstance number (arity + 1) (.lam name type expression bi)
  | apply (function : LiteralInstance number (arity + 1) expression) :
      LiteralInstance number arity (.app expression argument)
  | letE (body : LiteralInstance number arity expression) :
      LiteralInstance number arity (.letE name type value expression nondep)
  | metadata (body : LiteralInstance number arity expression) :
      LiteralInstance number arity (.mdata data expression)

theorem LiteralInstance.not_const {number arity expression}
    (evidence : LiteralInstance number arity expression) (name : Lean.Name) (levels : List Lean.Level) :
    expression ≠ .const name levels := by
  cases evidence <;> simp

end LeanExe.Source.Scalar
