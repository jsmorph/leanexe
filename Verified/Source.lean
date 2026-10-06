import LeanExe.Pipeline.Implements

/-! The source language of the verified compiler: functions whose body is a typed expression over
the function's arguments and `let`-bound values.  The types are 64-bit words and `Bool`, and an
expression of type `t` in a context `Γ` has type `Expr Γ t`, so every expression is well typed and
reads only variables in scope.  Each operation means Lean's operation: arithmetic wraps modulo
2^64, division by zero gives 0, the remainder by zero is the dividend, and a shift uses its amount
modulo 64. -/

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

/-- A comparison of words. -/
inductive CmpOp where
  | eq | ne | lt | le
  deriving Repr, DecidableEq

/-- Lean's comparison, unsigned. -/
def CmpOp.apply : CmpOp → UInt64 → UInt64 → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)

/-- The types of values. -/
inductive Ty where
  | word | bool
  deriving Repr, DecidableEq

/-- The Lean type of a value. -/
abbrev Ty.denote : Ty → Type
  | .word => UInt64
  | .bool => Bool

/-- The word that holds a value: a word itself, and 1 or 0 for a `Bool`, as `Implements` passes
a `Bool`. -/
def Ty.encode : (t : Ty) → t.denote → UInt64
  | .word, v => v
  | .bool, b => cond b 1 0

/-- A variable of type `t` in the context `Γ`, by its distance from the front of `Γ`. -/
inductive Var : List Ty → Ty → Type where
  | here : Var (t :: Γ) t
  | there : Var Γ t → Var (s :: Γ) t

def Var.index : Var Γ t → Nat
  | .here => 0
  | .there x => x.index + 1

/-- The variable at index `i`, given that `Γ` has type `t` there. -/
def Var.ofIndex : (Γ : List Ty) → (i : Nat) → Γ[i]? = some t → Var Γ t
  | _ :: _, 0, h => by simp at h; subst h; exact .here
  | _ :: Γ, i + 1, h => .there (Var.ofIndex Γ i (by simpa using h))
  | [], _, h => by simp at h

/-- Values for the variables of a context. -/
inductive Env : List Ty → Type where
  | nil : Env []
  | cons (v : t.denote) (env : Env Γ) : Env (t :: Γ)

def Env.get : {Γ : List Ty} → {t : Ty} → Env Γ → Var Γ t → t.denote
  | _, _, .cons v _, .here => v
  | _, _, .cons _ env, .there x => env.get x

/-- The words that hold the values, in order. -/
def Env.words : {Γ : List Ty} → Env Γ → List UInt64
  | _, .nil => []
  | _, .cons (t := t) v env => t.encode v :: env.words

/-- An expression of type `t` over the variables of `Γ`.  `letE value body` gives `body` the
value of `value` as variable 0, ahead of the variables of `Γ`. -/
inductive Expr : List Ty → Ty → Type where
  | word (value : UInt64) : Expr Γ .word
  | bool (value : Bool) : Expr Γ .bool
  | var (x : Var Γ t) : Expr Γ t
  | bin (op : BinOp) (left right : Expr Γ .word) : Expr Γ .word
  | cmp (op : CmpOp) (left right : Expr Γ .word) : Expr Γ .bool
  | not (e : Expr Γ .bool) : Expr Γ .bool
  | and (left right : Expr Γ .bool) : Expr Γ .bool
  | or (left right : Expr Γ .bool) : Expr Γ .bool
  | ite (c : Expr Γ .bool) (thenE elseE : Expr Γ t) : Expr Γ t
  | letE (value : Expr Γ s) (body : Expr (s :: Γ) t) : Expr Γ t

/-- Variable `i` of a context known when the expression is written. -/
abbrev Expr.v {Γ : List Ty} {t : Ty} (i : Nat) (h : Γ[i]? = some t := by rfl) : Expr Γ t :=
  .var (Var.ofIndex Γ i h)

/-- The value of an expression for the values `env` of its variables. -/
def Expr.denote : {Γ : List Ty} → {t : Ty} → Expr Γ t → Env Γ → t.denote
  | _, _, .word value, _ => value
  | _, _, .bool value, _ => value
  | _, _, .var x, env => env.get x
  | _, _, .bin op left right, env => op.apply (left.denote env) (right.denote env)
  | _, _, .cmp op left right, env => op.apply (left.denote env) (right.denote env)
  | _, _, .not e, env => !e.denote env
  | _, _, .and left right, env => left.denote env && right.denote env
  | _, _, .or left right, env => left.denote env || right.denote env
  | _, _, .ite c thenE elseE, env => if c.denote env then thenE.denote env else elseE.denote env
  | _, _, .letE value body, env => body.denote (.cons (value.denote env) env)

/-- A function whose parameters have the types `params`, in order, and whose body has type
`result`.  Parameter `i` is variable `i` of the body. -/
structure Func where
  params : List Ty
  result : Ty
  body : Expr params result

/-- The arguments of a function, one word each, in order. -/
instance : Scalar (Env Γ) := ⟨fun env => env.words.map Value.i64⟩

/-- A value is passed as the word that holds it. -/
instance (t : Ty) : Scalar t.denote := ⟨fun v => [.i64 (t.encode v)]⟩

/-- The Lean function that `func` means. -/
def Func.denote (func : Func) (args : Env func.params) : func.result.denote :=
  func.body.denote args

end Verified
