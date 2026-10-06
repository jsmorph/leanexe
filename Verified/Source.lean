import LeanExe.Pipeline.Implements

/-! The source language of the verified compiler: functions whose body is an expression on
64-bit words over the function's arguments.  Each operation means Lean's operation on `UInt64`:
arithmetic wraps modulo 2^64, division by zero gives 0, the remainder by zero is the dividend,
and a shift uses its amount modulo 64. -/

namespace Verified

open Wasm LeanExe.Pipeline

/-- A binary operation on words. -/
inductive BinOp where
  | add | sub | mul | div | rem | and | or | xor | shl | shr
  deriving Repr, DecidableEq

/-- Lean's operation. -/
def BinOp.apply : BinOp → UInt64 → UInt64 → UInt64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .rem, a, b => a % b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b
  | .shr, a, b => a >>> b

/-- An expression over the arguments of a function. -/
inductive Expr where
  | const (value : UInt64)
  | arg (index : Nat)
  | bin (op : BinOp) (left right : Expr)
  deriving Repr

/-- The value of an expression for the arguments `args`.  An argument past the end reads 0, and
`Expr.argsBelow` excludes such reads from compiled functions. -/
def Expr.denote (args : List UInt64) : Expr → UInt64
  | .const value => value
  | .arg index => args.getD index 0
  | .bin op left right => op.apply (left.denote args) (right.denote args)

/-- Every argument that the expression reads is below `arity`. -/
def Expr.argsBelow (arity : Nat) : Expr → Bool
  | .const _ => true
  | .arg index => index < arity
  | .bin _ left right => left.argsBelow arity && right.argsBelow arity

/-- A function of `arity` word arguments that returns the value of `body`. -/
structure Func where
  arity : Nat
  body : Expr

/-- The arguments of a function, one word each, in order. -/
instance : Scalar (Vector UInt64 n) := ⟨fun args => args.toList.map Value.i64⟩

/-- The Lean function that `func` means. -/
def Func.denote (func : Func) (args : Vector UInt64 func.arity) : UInt64 :=
  func.body.denote args.toList

end Verified
