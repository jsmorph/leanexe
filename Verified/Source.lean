import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! The source language of the verified compiler: functions whose body is a typed expression over
the function's arguments and the values that bindings and loops introduce.  The types are 64-bit
words, `Bool`s, floats, tuples of these, pairs, and arrays, and an expression of type `t` in a
context `Γ` that may call functions
with the signatures `S` has type `Expr S Γ t`, so every expression is well typed, reads only
variables in scope, and calls only functions that exist.  Each operation means Lean's operation:
arithmetic wraps modulo 2^64, division by zero gives 0, the remainder by zero is the dividend, and
a shift uses its amount modulo 64. -/

namespace Verified

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

/-- A binary operation on floats. -/
inductive FBinOp where
  | add | sub | mul | div
  deriving Repr, DecidableEq

/-- Lean's operation, binary64 with rounding to nearest. -/
def FBinOp.apply : FBinOp → Float → Float → Float
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- An operation on one float: the square root, the absolute value, and the negation. -/
inductive FUnOp where
  | sqrt | abs | neg
  deriving Repr, DecidableEq

def FUnOp.apply : FUnOp → Float → Float
  | .sqrt, a => a.sqrt
  | .abs, a => a.abs
  | .neg, a => -a

/-- A comparison of floats, false when an operand is NaN. -/
inductive FCmpOp where
  | lt | le | eq
  deriving Repr, DecidableEq

def FCmpOp.apply : FCmpOp → Float → Float → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .eq, a, b => a == b

/-- A conversion of a word to a float: `UInt64.toFloat`, rounded to nearest, and `Float.ofBits`,
which gives the canonical NaN for every NaN pattern. -/
inductive ToFloat where
  | convert | ofBits
  deriving Repr, DecidableEq

def ToFloat.apply : ToFloat → UInt64 → Float
  | .convert, a => a.toFloat
  | .ofBits, a => Float.ofBits a

/-- A conversion of a float to a word: `Float.toUInt64`, which truncates toward zero and
saturates, with 0 for NaN, and `Float.toBits`. -/
inductive ToWord where
  | truncate | toBits
  deriving Repr, DecidableEq

def ToWord.apply : ToWord → Float → UInt64
  | .truncate, a => a.toUInt64
  | .toBits, a => a.toBits

/-- The types of the values that hold no arrays and that an array may hold: words, `Bool`s,
floats, and tuples of these. -/
inductive Elem where
  | word | bool | float
  | prod (first second : Elem)
  deriving Repr, DecidableEq, Inhabited

/-- The types of values: the element types, pairs, which may hold arrays, and arrays of an element
type. -/
inductive Ty where
  | elem (e : Elem)
  | pair (first second : Ty)
  | array (e : Elem)
  deriving Repr, DecidableEq, Inhabited

@[match_pattern] abbrev Ty.word : Ty := .elem .word
@[match_pattern] abbrev Ty.bool : Ty := .elem .bool
@[match_pattern] abbrev Ty.float : Ty := .elem .float

/-- The Lean type of an element. -/
abbrev Elem.denote : Elem → Type
  | .word => UInt64
  | .bool => Bool
  | .float => Float
  | .prod a b => a.denote × b.denote

/-- The Lean type of a value. -/
abbrev Ty.denote : Ty → Type
  | .elem e => e.denote
  | .pair a b => a.denote × b.denote
  | .array e => Array e.denote

/-- Lean's default value of an element type, which a read past the end of an array gives. -/
instance Elem.instInhabited : (e : Elem) → Inhabited e.denote
  | .word => inferInstanceAs (Inhabited UInt64)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .float => inferInstanceAs (Inhabited Float)
  | .prod a b => ⟨(@default _ a.instInhabited, @default _ b.instInhabited)⟩

/-- The word that holds a `Bool`: 1 or 0, as `Implements` passes a `Bool`. -/
def boolWord (b : Bool) : UInt64 := cond b 1 0

/-- The number of words that hold an element. -/
def Elem.width : Elem → Nat
  | .word | .bool | .float => 1
  | .prod a b => a.width + b.width

@[simp] theorem Elem.width_word : Elem.width .word = 1 := rfl
@[simp] theorem Elem.width_bool : Elem.width .bool = 1 := rfl
@[simp] theorem Elem.width_float : Elem.width .float = 1 := rfl

/-- The words that hold an element in an array, in order: a word as itself, a `Bool` as 1 or 0,
a float as its bit pattern, and a tuple as its first part's words followed by its second's. -/
def Elem.toWords : (e : Elem) → e.denote → List UInt64
  | .word, x => [x]
  | .bool, b => [boolWord b]
  | .float, x => [x.toBits]
  | .prod a b, v => a.toWords v.1 ++ b.toWords v.2

/-- A component of type `e'` of an element of type `e`: the element, or a component of its first
or its second part. -/
inductive Path : Elem → Elem → Type where
  | here : Path e e
  | fst (p : Path a e) : Path (.prod a b) e
  | snd (p : Path b e) : Path (.prod a b) e

def Path.get : {e e' : Elem} → Path e e' → e.denote → e'.denote
  | _, _, .here, v => v
  | _, _, .fst p, v => p.get v.1
  | _, _, .snd p, v => p.get v.2

/-- The number of words of an element before its component. -/
def Path.offset : {e e' : Elem} → Path e e' → Nat
  | _, _, .here => 0
  | _, _, .fst p => p.offset
  | _, _, .snd (a := a) p => a.width + p.offset

/-- The number of words that hold a value of the type. -/
def Ty.width : Ty → Nat
  | .elem e => e.width
  | .array _ => 1
  | .pair a b => a.width + b.width

/-- Whether a type holds no arrays. -/
def Ty.scalar : Ty → Bool
  | .elem _ => true
  | .pair a b => a.scalar && b.scalar
  | .array _ => false

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

/-- The values of a context, given by index. -/
def Env.ofFn : {Γ : List Ty} → ((i : Fin Γ.length) → (Γ.get i).denote) → Env Γ
  | [], _ => .nil
  | _ :: _, f => .cons (f ⟨0, by simp⟩) (Env.ofFn fun i => f i.succ)

/-- How a variable holds an array: borrowed, readable while the variable is in scope, or owned,
which its holder must consume. -/
inductive Mode where
  | borrowed | owned
  deriving DecidableEq, Repr, Inhabited

/-- The mode of a parameter of type `t` for which the mode `m` was chosen: only an array
parameter is owned. -/
def Ty.paramMode : Ty → Mode → Mode
  | .array _, m => m
  | _, _ => .borrowed

/-- The modes of parameters of types `ts` for which the modes `ms` were chosen, in order, a missing
choice borrowed. -/
def paramModes : List Ty → List Mode → List Mode
  | [], _ => []
  | t :: ts, ms => t.paramMode (ms.headD .borrowed) :: paramModes ts ms.tail

/-- The mode of parameter `i` among parameters of types `ts` for which the modes `ms` were
chosen. -/
def paramMode (ts : List Ty) (ms : List Mode) (i : Nat) : Mode :=
  (paramModes ts ms).getD i .borrowed

/-- The signature of a function: its parameter types, its result type, whether a call may trap
at `unreachable`, which only a function that allocates, directly or through a call, does, and the
modes chosen for its parameters.  The call consumes the arrays of its owned parameters. -/
structure Sig where
  params : List Ty
  result : Ty
  aborts : Bool
  modes : List Mode
  deriving DecidableEq

/-- The modes of the parameters of the signature `g`, by index. -/
def Sig.mode (g : Sig) : Nat → Mode := paramMode g.params g.modes

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
index as variable 1.  `size x` is the number of elements of the array variable `x` as a word,
and `get x i` is element `i` of `x`, or the element type's default value when `i` is not below
the size, as Lean's `x[i.toNat]!` gives.  `build count elem` is `LeanExe.build`: the array of
`count` elements whose element `i` is the value of `elem` with `i` as variable 0.  `set x i v` is
`x.set! i.toNat v`:
the array of `x` with element `i` replaced by `v`, or `x` when `i` is not below the size.
`push x v` is `x.push v`, and `append x y` is `x ++ y`.  `float bits` is the float with the bit
pattern `bits`, `fbin`, `funary`, and `fcmp` are the operations and comparisons of floats, and
`toFloat` and `toWord` convert between words and floats.  `mk first second` is the tuple of two
elements, and `proj x p` is the component at path `p` of the tuple variable `x`. -/
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
  | size (x : Var Γ (.array e)) : Expr S Γ .word
  | get (x : Var Γ (.array e)) (i : Expr S Γ .word) : Expr S Γ (.elem e)
  | build (count : Expr S Γ .word) (elem : Expr S (.word :: Γ) (.elem e)) : Expr S Γ (.array e)
  | set (x : Var Γ (.array e)) (i : Expr S Γ .word) (v : Expr S Γ (.elem e)) :
      Expr S Γ (.array e)
  | push (x : Var Γ (.array e)) (v : Expr S Γ (.elem e)) : Expr S Γ (.array e)
  | append (x y : Var Γ (.array e)) : Expr S Γ (.array e)
  | float (bits : UInt64) : Expr S Γ .float
  | fbin (op : FBinOp) (left right : Expr S Γ .float) : Expr S Γ .float
  | funary (op : FUnOp) (e : Expr S Γ .float) : Expr S Γ .float
  | fcmp (op : FCmpOp) (left right : Expr S Γ .float) : Expr S Γ .bool
  | toFloat (op : ToFloat) (e : Expr S Γ .word) : Expr S Γ .float
  | toWord (op : ToWord) (e : Expr S Γ .float) : Expr S Γ .word
  | mk (first : Expr S Γ (.elem a)) (second : Expr S Γ (.elem b)) : Expr S Γ (.elem (.prod a b))
  | proj (x : Var Γ (.elem e)) (p : Path e e') : Expr S Γ (.elem e')

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
  | _, _, .size x, env => (env.get x).size.toUInt64
  | _, _, .get x i, env => (env.get x)[(i.denote funs env).toNat]!
  | _, _, .build count elem, env =>
    LeanExe.build (count.denote funs env) fun i => elem.denote funs (.cons i env)
  | _, _, .set x i v, env => (env.get x).set! (i.denote funs env).toNat (v.denote funs env)
  | _, _, .push x v, env => (env.get x).push (v.denote funs env)
  | _, _, .append x y, env => env.get x ++ env.get y
  | _, _, .float bits, _ => Float.ofBits bits
  | _, _, .fbin op left right, env => op.apply (left.denote funs env) (right.denote funs env)
  | _, _, .funary op e, env => op.apply (e.denote funs env)
  | _, _, .fcmp op left right, env => op.apply (left.denote funs env) (right.denote funs env)
  | _, _, .toFloat op e, env => op.apply (e.denote funs env)
  | _, _, .toWord op e, env => op.apply (e.denote funs env)
  | _, _, .mk first second, env => (first.denote funs env, second.denote funs env)
  | _, _, .proj x p, env => p.get (env.get x)

/-- Whether any of the values `b i` is true. -/
def argsAny : {n : Nat} → ((i : Fin n) → Bool) → Bool
  | 0, _ => false
  | _ + 1, b => b 0 || argsAny fun i => b i.succ

/-- Whether the code of an expression may trap: whether it builds, updates, or extends an array,
which may allocate, or calls a function that may trap, that returns arrays, or that owns a
parameter, whose argument the call may copy, since only these allocate. -/
def Expr.aborts : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ | _, _, .float _ => false
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right => left.aborts || right.aborts
  | _, _, .toFloat _ e => e.aborts
  | _, _, .toWord _ e => e.aborts
  | _, _, .mk first second => first.aborts || second.aborts
  | _, _, .proj _ _ => false
  | _, _, .funary _ e => e.aborts
  | _, _, .not e => e.aborts
  | _, _, .and left right | _, _, .or left right => left.aborts || right.aborts
  | _, _, .ite c thenE elseE => c.aborts || thenE.aborts || elseE.aborts
  | _, _, .letE value body => value.aborts || body.aborts
  | _, _, .call (g := g) _ args =>
    g.aborts || !g.result.scalar || argsAny fun i => (args i).aborts || g.mode i == .owned
  | _, _, .pair first second => first.aborts || second.aborts
  | _, _, .letPair e body => e.aborts || body.aborts
  | _, _, .loop count init body => count.aborts || init.aborts || body.aborts
  | _, _, .size _ => false
  | _, _, .get _ i => i.aborts
  | _, _, .build _ _ | _, _, .set _ _ _ | _, _, .push _ _ | _, _, .append _ _ => true

/-- The variables that an expression reads, by index. -/
def Expr.uses : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat → Bool
  | _, _, .word _, _ | _, _, .bool _, _ | _, _, .float _, _ => false
  | _, _, .var x, i => i == x.index
  | _, _, .bin _ left right, i | _, _, .cmp _ left right, i | _, _, .fbin _ left right, i
  | _, _, .fcmp _ left right, i => left.uses i || right.uses i
  | _, _, .toFloat _ e, i => e.uses i
  | _, _, .toWord _ e, i => e.uses i
  | _, _, .mk first second, i => first.uses i || second.uses i
  | _, _, .proj x _, i => i == x.index
  | _, _, .funary _ e, i => e.uses i
  | _, _, .not e, i => e.uses i
  | _, _, .and left right, i | _, _, .or left right, i => left.uses i || right.uses i
  | _, _, .ite c thenE elseE, i => c.uses i || thenE.uses i || elseE.uses i
  | _, _, .letE value body, i => value.uses i || body.uses (i + 1)
  | _, _, .call _ args, i => argsAny fun j => (args j).uses i
  | _, _, .pair first second, i => first.uses i || second.uses i
  | _, _, .letPair e body, i => e.uses i || body.uses (i + 2)
  | _, _, .loop count init body, i => count.uses i || init.uses i || body.uses (i + 2)
  | _, _, .size x, i => i == x.index
  | _, _, .get x k, i => i == x.index || k.uses i
  | _, _, .build count elem, i => count.uses i || elem.uses (i + 1)
  | _, _, .set x k v, i => i == x.index || k.uses i || v.uses i
  | _, _, .push x v, i => i == x.index || v.uses i
  | _, _, .append x y, i => i == x.index || i == y.index

/-- The index of an expression that is a variable. -/
def Expr.varIndex? : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Option Nat
  | _, _, .var x => some x.index
  | _, _, _ => none

/-- Whether an expression is a variable or a pair of such expressions, which a call reads in
place. -/
def Expr.isPlace : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .var _ => true
  | _, _, .pair first second => first.isPlace && second.isPlace
  | _, _, _ => false

/-- Whether every argument of every call in an expression that holds arrays is a variable or a
pair of such arguments, and a variable at an owned parameter.  The reflector binds any other such
argument with `let`. -/
def Expr.placeArgs : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ | _, _, .size _ | _, _, .float _ => true
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right => left.placeArgs && right.placeArgs
  | _, _, .toFloat _ e => e.placeArgs
  | _, _, .toWord _ e => e.placeArgs
  | _, _, .mk first second => first.placeArgs && second.placeArgs
  | _, _, .proj _ _ => true
  | _, _, .funary _ e => e.placeArgs
  | _, _, .not e => e.placeArgs
  | _, _, .and left right | _, _, .or left right => left.placeArgs && right.placeArgs
  | _, _, .ite c thenE elseE => c.placeArgs && thenE.placeArgs && elseE.placeArgs
  | _, _, .letE value body => value.placeArgs && body.placeArgs
  | _, _, .call (g := g) _ args =>
    argsAny (fun i => !(g.params.get i).scalar && !(args i).isPlace) == false &&
      argsAny (fun i => g.mode i == .owned && (args i).varIndex?.isNone) == false &&
      !(argsAny fun i => !(args i).placeArgs)
  | _, _, .pair first second => first.placeArgs && second.placeArgs
  | _, _, .letPair e body => e.placeArgs && body.placeArgs
  | _, _, .loop count init body => count.placeArgs && init.placeArgs && body.placeArgs
  | _, _, .get _ i => i.placeArgs
  | _, _, .build count elem => count.placeArgs && elem.placeArgs
  | _, _, .set _ i v => i.placeArgs && v.placeArgs
  | _, _, .push _ v => v.placeArgs
  | _, _, .append _ _ => true

/-- A function named `name`, whose parameters have the types `params`, in order, and whose body
has type `result` and may call the functions `S`.  Parameter `i` is variable `i` of the body, held
in the mode that `modes` chooses for it.  The arguments of the body's calls that hold arrays are
variables or pairs of variables. -/
structure Func (S : List Sig) where
  name : String
  params : List Ty
  result : Ty
  body : Expr S params result
  placeArgs : body.placeArgs = true
  modes : List Mode

/-- Whether a call of the function may trap: whether its body may, its result holds arrays, which
a borrowed result's copy allocates, or a parameter is owned, whose variable the body may copy. -/
def Func.aborts (func : Func S) : Bool :=
  func.body.aborts || !func.result.scalar || (paramModes func.params func.modes).any (· == .owned)

/-- The Lean function that `func` means, given the Lean functions that it calls. -/
def Func.denote (func : Func S) (funs : Funs S) (args : Env func.params) : func.result.denote :=
  func.body.denote funs args

/-- A program: functions in which each may call the functions after it in the list, which come
before it in the module. -/
inductive Prog : List Sig → Type where
  | nil : Prog []
  | cons (f : Func S) (rest : Prog S) : Prog (⟨f.params, f.result, f.aborts, f.modes⟩ :: S)

/-- The Lean functions that a program's functions mean. -/
def Prog.funs : {S : List Sig} → Prog S → Funs S
  | _, .nil => .nil
  | _, .cons f rest => .cons (f.denote rest.funs) rest.funs

end Verified
