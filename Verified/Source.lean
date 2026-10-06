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

/-- The values of a context, given by index. -/
def Env.ofFn : {Γ : List Ty} → ((i : Fin Γ.length) → (Γ.get i).denote) → Env Γ
  | [], _ => .nil
  | _ :: _, f => .cons (f ⟨0, by simp⟩) (Env.ofFn fun i => f i.succ)

/-- The signature of a function: its parameter types and its result type. -/
abbrev Sig := List Ty × Ty

/-- A function of signature `(ps, r)` among the functions `S` that an expression may call, by
its distance from the front of `S`. -/
inductive FVar : List Sig → List Ty → Ty → Type where
  | here : FVar ((ps, r) :: S) ps r
  | there : FVar S ps r → FVar (g :: S) ps r

def FVar.index : FVar S ps r → Nat
  | .here => 0
  | .there f => f.index + 1

/-- The function at index `i`, given that `S` has signature `(ps, r)` there. -/
def FVar.ofIndex : (S : List Sig) → (i : Nat) → S[i]? = some (ps, r) → FVar S ps r
  | _ :: _, 0, h => by simp at h; obtain ⟨rfl, rfl⟩ := h; exact .here
  | _ :: S, i + 1, h => .there (FVar.ofIndex S i (by simpa using h))
  | [], _, h => by simp at h

/-- Lean functions with the signatures `S`. -/
inductive Funs : List Sig → Type where
  | nil : Funs []
  | cons (f : Env ps → r.denote) (rest : Funs S) : Funs ((ps, r) :: S)

def Funs.get : {S : List Sig} → {ps : List Ty} → {r : Ty} →
    Funs S → FVar S ps r → Env ps → r.denote
  | _, _, _, .cons f _, .here => f
  | _, _, _, .cons _ rest, .there g => rest.get g

/-- An expression of type `t` over the variables of `Γ` that may call the functions `S`.
`letE value body` gives `body` the value of `value` as variable 0, ahead of the variables of `Γ`.
`call f args` applies function `f` to the values of `args`, argument `i` having the type of
parameter `i`. -/
inductive Expr (S : List Sig) : List Ty → Ty → Type where
  | word (value : UInt64) : Expr S Γ .word
  | bool (value : Bool) : Expr S Γ .bool
  | var (x : Var Γ t) : Expr S Γ t
  | bin (op : BinOp) (left right : Expr S Γ .word) : Expr S Γ .word
  | cmp (op : CmpOp) (left right : Expr S Γ .word) : Expr S Γ .bool
  | not (e : Expr S Γ .bool) : Expr S Γ .bool
  | and (left right : Expr S Γ .bool) : Expr S Γ .bool
  | or (left right : Expr S Γ .bool) : Expr S Γ .bool
  | ite (c : Expr S Γ .bool) (thenE elseE : Expr S Γ t) : Expr S Γ t
  | letE (value : Expr S Γ s) (body : Expr S (s :: Γ) t) : Expr S Γ t
  | call (f : FVar S ps r) (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) : Expr S Γ r

/-- Variable `i` of a context known when the expression is written. -/
abbrev Expr.v {S : List Sig} {Γ : List Ty} {t : Ty} (i : Nat) (h : Γ[i]? = some t := by rfl) :
    Expr S Γ t :=
  .var (Var.ofIndex Γ i h)

/-- The arguments of a call, in order. -/
inductive Args (S : List Sig) (Γ : List Ty) : List Ty → Type where
  | nil : Args S Γ []
  | cons (e : Expr S Γ t) (rest : Args S Γ ts) : Args S Γ (t :: ts)

def Args.get : {ps : List Ty} → Args S Γ ps → (i : Fin ps.length) → Expr S Γ (ps.get i)
  | _ :: _, .cons e _, ⟨0, _⟩ => e
  | _ :: _, .cons _ rest, ⟨i + 1, h⟩ => rest.get ⟨i, by simpa using h⟩

/-- A call of function `i` of a list of functions known when the expression is written. -/
abbrev Expr.app {S : List Sig} {Γ ps : List Ty} {r : Ty} (i : Nat) (args : Args S Γ ps)
    (h : S[i]? = some (ps, r) := by rfl) : Expr S Γ r :=
  .call (FVar.ofIndex S i h) args.get

/-- The value of an expression for the functions `funs` and the values `env` of its
variables. -/
def Expr.denote (funs : Funs S) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → t.denote
  | _, _, .word value, _ => value
  | _, _, .bool value, _ => value
  | _, _, .var x, env => env.get x
  | _, _, .bin op left right, env => op.apply (left.denote funs env) (right.denote funs env)
  | _, _, .cmp op left right, env => op.apply (left.denote funs env) (right.denote funs env)
  | _, _, .not e, env => !e.denote funs env
  | _, _, .and left right, env => left.denote funs env && right.denote funs env
  | _, _, .or left right, env => left.denote funs env || right.denote funs env
  | _, _, .ite c thenE elseE, env =>
    if c.denote funs env then thenE.denote funs env else elseE.denote funs env
  | _, _, .letE value body, env => body.denote funs (.cons (value.denote funs env) env)
  | _, _, .call f args, env => funs.get f (Env.ofFn fun i => (args i).denote funs env)

/-- A function named `name`, whose parameters have the types `params`, in order, and whose body
has type `result` and may call the functions `S`.  Parameter `i` is variable `i` of the body. -/
structure Func (S : List Sig) where
  name : String
  params : List Ty
  result : Ty
  body : Expr S params result

/-- The arguments of a function, one word each, in order. -/
instance : Scalar (Env Γ) := ⟨fun env => env.words.map Value.i64⟩

/-- A value is passed as the word that holds it. -/
instance (t : Ty) : Scalar t.denote := ⟨fun v => [.i64 (t.encode v)]⟩

/-- The Lean function that `func` means, given the Lean functions that it calls. -/
def Func.denote (func : Func S) (funs : Funs S) (args : Env func.params) : func.result.denote :=
  func.body.denote funs args

/-- A program: functions in which each may call the functions after it in the list, which come
before it in the module. -/
inductive Prog : List Sig → Type where
  | nil : Prog []
  | cons (f : Func S) (rest : Prog S) : Prog ((f.params, f.result) :: S)

/-- The Lean functions that a program's functions mean. -/
def Prog.funs : {S : List Sig} → Prog S → Funs S
  | _, .nil => .nil
  | _, .cons f rest => .cons (f.denote rest.funs) rest.funs

end Verified
