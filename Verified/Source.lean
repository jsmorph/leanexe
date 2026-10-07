import LeanExe.Pipeline.Implements
import LeanExe.Dialect.Loop

/-! The source language of the verified compiler: functions whose body is a typed expression over
the function's arguments and the values that bindings and loops introduce.  The types are 64-bit
words, `Bool`, and pairs, and an expression of type `t` in a context `Γ` that may call functions
with the signatures `S` has type `Expr S Γ t`, so every expression is well typed, reads only
variables in scope, and calls only functions that exist.  Each operation means Lean's operation:
arithmetic wraps modulo 2^64, division by zero gives 0, the remainder by zero is the dividend, and
a shift uses its amount modulo 64. -/

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

/-- The types of values: words, `Bool`s, and pairs. -/
inductive Ty where
  | word | bool
  | pair (first second : Ty)
  deriving Repr, DecidableEq, Inhabited

/-- The Lean type of a value. -/
abbrev Ty.denote : Ty → Type
  | .word => UInt64
  | .bool => Bool
  | .pair a b => a.denote × b.denote

/-- The word that holds a `Bool`: 1 or 0, as `Implements` passes a `Bool`. -/
def boolWord (b : Bool) : UInt64 := cond b 1 0

/-- The number of words that hold a value of the type. -/
def Ty.width : Ty → Nat
  | .word | .bool => 1
  | .pair a b => a.width + b.width

/-- The words that hold a value, as `Implements` passes it: a pair is its first component's
words followed by its second's. -/
def Ty.values : (t : Ty) → t.denote → List Value
  | .word, v => [.i64 v]
  | .bool, b => [.i64 (boolWord b)]
  | .pair a b, p => a.values p.1 ++ b.values p.2

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
def Env.values : {Γ : List Ty} → Env Γ → List Value
  | _, .nil => []
  | _, .cons (t := t) v env => t.values v ++ env.values

/-- The values of a context, given by index. -/
def Env.ofFn : {Γ : List Ty} → ((i : Fin Γ.length) → (Γ.get i).denote) → Env Γ
  | [], _ => .nil
  | _ :: _, f => .cons (f ⟨0, by simp⟩) (Env.ofFn fun i => f i.succ)

/-- The signature of a function: its parameter types, its result type, and whether a call may
trap at `unreachable`, which only a function that allocates, directly or through a call, does. -/
structure Sig where
  params : List Ty
  result : Ty
  aborts : Bool
  deriving DecidableEq

/-- A function with signature `g` among the functions `S` that an expression may call, by its
distance from the front of `S`. -/
inductive FVar : List Sig → Sig → Type where
  | here : FVar (g :: S) g
  | there : FVar S g → FVar (h :: S) g

def FVar.index : FVar S g → Nat
  | .here => 0
  | .there f => f.index + 1

/-- The function at index `i`, given that `S` has signature `g` there. -/
def FVar.ofIndex : (S : List Sig) → (i : Nat) → S[i]? = some g → FVar S g
  | _ :: _, 0, h => by simp at h; subst h; exact .here
  | _ :: S, i + 1, h => .there (FVar.ofIndex S i (by simpa using h))
  | [], _, h => by simp at h

/-- Lean functions with the signatures `S`. -/
inductive Funs : List Sig → Type where
  | nil : Funs []
  | cons (f : Env g.params → g.result.denote) (rest : Funs S) : Funs (g :: S)

def Funs.get : {S : List Sig} → {g : Sig} → Funs S → FVar S g → Env g.params →
    g.result.denote
  | _, _, .cons f _, .here => f
  | _, _, .cons _ rest, .there h => rest.get h

/-- An expression of type `t` over the variables of `Γ` that may call the functions `S`.
`letE value body` gives `body` the value of `value` as variable 0, ahead of the variables of `Γ`.
`call f args` applies function `f` to the values of `args`, argument `i` having the type of
parameter `i`.  `letPair e body` gives `body` the second component of `e` as variable 0 and the
first as variable 1.  `loop count init body` is `LeanExe.loop`: starting from the value of
`init`, it applies `body` to the indices 0 to `count - 1`, with the state as variable 0 and the
index as variable 1. -/
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
  | call (f : FVar S g) (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) :
      Expr S Γ g.result
  | pair (first : Expr S Γ s) (second : Expr S Γ t) : Expr S Γ (.pair s t)
  | letPair (e : Expr S Γ (.pair s t)) (body : Expr S (t :: s :: Γ) u) : Expr S Γ u
  | loop (count : Expr S Γ .word) (init : Expr S Γ t) (body : Expr S (t :: .word :: Γ) t) :
      Expr S Γ t

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
abbrev Expr.app {S : List Sig} {Γ : List Ty} {g : Sig} (i : Nat) (args : Args S Γ g.params)
    (h : S[i]? = some g := by rfl) : Expr S Γ g.result :=
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
  | _, _, .pair first second, env => (first.denote funs env, second.denote funs env)
  | _, _, .letPair e body, env =>
    let p := e.denote funs env
    body.denote funs (.cons p.2 (.cons p.1 env))
  | _, _, .loop count init body, env =>
    LeanExe.loop (count.denote funs env) (init.denote funs env)
      fun i acc => body.denote funs (.cons acc (.cons i env))

/-- Whether any of the values `b i` is true. -/
def argsAny : {n : Nat} → ((i : Fin n) → Bool) → Bool
  | 0, _ => false
  | _ + 1, b => b 0 || argsAny fun i => b i.succ

/-- Whether the code of an expression may trap: whether it calls a function that may. -/
def Expr.aborts : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ => false
  | _, _, .bin _ left right | _, _, .cmp _ left right => left.aborts || right.aborts
  | _, _, .not e => e.aborts
  | _, _, .and left right | _, _, .or left right => left.aborts || right.aborts
  | _, _, .ite c thenE elseE => c.aborts || thenE.aborts || elseE.aborts
  | _, _, .letE value body => value.aborts || body.aborts
  | _, _, .call (g := g) _ args => g.aborts || argsAny fun i => (args i).aborts
  | _, _, .pair first second => first.aborts || second.aborts
  | _, _, .letPair e body => e.aborts || body.aborts
  | _, _, .loop count init body => count.aborts || init.aborts || body.aborts

/-- The variables that an expression reads, by index. -/
def Expr.uses : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat → Bool
  | _, _, .word _, _ | _, _, .bool _, _ => false
  | _, _, .var x, i => i == x.index
  | _, _, .bin _ left right, i | _, _, .cmp _ left right, i => left.uses i || right.uses i
  | _, _, .not e, i => e.uses i
  | _, _, .and left right, i | _, _, .or left right, i => left.uses i || right.uses i
  | _, _, .ite c thenE elseE, i => c.uses i || thenE.uses i || elseE.uses i
  | _, _, .letE value body, i => value.uses i || body.uses (i + 1)
  | _, _, .call _ args, i => argsAny fun j => (args j).uses i
  | _, _, .pair first second, i => first.uses i || second.uses i
  | _, _, .letPair e body, i => e.uses i || body.uses (i + 2)
  | _, _, .loop count init body, i => count.uses i || init.uses i || body.uses (i + 2)

/-- A function named `name`, whose parameters have the types `params`, in order, and whose body
has type `result` and may call the functions `S`.  Parameter `i` is variable `i` of the body. -/
structure Func (S : List Sig) where
  name : String
  params : List Ty
  result : Ty
  body : Expr S params result

/-- The arguments of a function, as the words that hold them, in order. -/
instance : Scalar (Env Γ) := ⟨Env.values⟩

/-- A value is passed as the words that hold it. -/
instance (t : Ty) : Scalar t.denote := ⟨t.values⟩

/-- The Lean function that `func` means, given the Lean functions that it calls. -/
def Func.denote (func : Func S) (funs : Funs S) (args : Env func.params) : func.result.denote :=
  func.body.denote funs args

/-- A program: functions in which each may call the functions after it in the list, which come
before it in the module. -/
inductive Prog : List Sig → Type where
  | nil : Prog []
  | cons (f : Func S) (rest : Prog S) : Prog (⟨f.params, f.result, f.body.aborts⟩ :: S)

/-- The Lean functions that a program's functions mean. -/
def Prog.funs : {S : List Sig} → Prog S → Funs S
  | _, .nil => .nil
  | _, .cons f rest => .cons (f.denote rest.funs) rest.funs

end Verified
