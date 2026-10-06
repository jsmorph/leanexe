import LeanExe.Pipeline.Implements

/-! The source language of the verified compiler: functions whose body is an expression on
64-bit words over the function's arguments.  Arithmetic wraps modulo 2^64, as Lean's `UInt64`
does. -/

namespace Verified

open Wasm LeanExe.Pipeline

/-- An expression over the arguments of a function. -/
inductive Expr where
  | const (value : UInt64)
  | arg (index : Nat)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  deriving Repr

/-- The value of an expression for the arguments `args`.  An argument past the end reads 0, and
`Expr.argsBelow` excludes such reads from compiled functions. -/
def Expr.denote (args : List UInt64) : Expr → UInt64
  | .const value => value
  | .arg index => args.getD index 0
  | .add left right => left.denote args + right.denote args
  | .sub left right => left.denote args - right.denote args
  | .mul left right => left.denote args * right.denote args

/-- Every argument that the expression reads is below `arity`. -/
def Expr.argsBelow (arity : Nat) : Expr → Bool
  | .const _ => true
  | .arg index => index < arity
  | .add left right | .sub left right | .mul left right =>
    left.argsBelow arity && right.argsBelow arity

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
