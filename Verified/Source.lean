import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.InsertErase
import LeanExe.Dialect.Float32
import LeanExe.Dialect.Bytes
import Verified.Tree
import Verified.TreeFold

/-! The source language of the verified compiler: functions whose body is a typed expression over
the function's arguments and the values that bindings and loops introduce.  The types are 64-bit
words, `Bool`s, floats, tuples of these, pairs, arrays, packed bytes, and fixed-layout recursive trees.  An expression of type `t` in a
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

def FBinOp.apply32 : FBinOp → Float32 → Float32 → Float32
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

inductive F32UnOp where
  | sqrt | abs | neg | nearest
  deriving Repr, DecidableEq

def F32UnOp.apply : F32UnOp → Float32 → Float32
  | .sqrt, a => a.sqrt
  | .abs, a => a.abs
  | .neg, a => -a
  | .nearest, a => LeanExe.Float32.nearest a

/-- A comparison of floats, false when an operand is NaN. -/
inductive FCmpOp where
  | lt | le | eq
  deriving Repr, DecidableEq

def FCmpOp.apply : FCmpOp → Float → Float → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .eq, a, b => a == b

def FCmpOp.apply32 : FCmpOp → Float32 → Float32 → Bool
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

inductive ToFloat32 where
  | convert | ofBits | signed32
  deriving Repr, DecidableEq

def ToFloat32.apply : ToFloat32 → UInt64 → Float32
  | .convert, a => a.toFloat32
  | .ofBits, a => Float32.ofBits a.toUInt32
  | .signed32, a => (Int32.ofUInt32 a.toUInt32).toFloat32

inductive ToWord32 where
  | truncate | toBits | signed32
  deriving Repr, DecidableEq

def ToWord32.apply : ToWord32 → Float32 → UInt64
  | .truncate, a => a.toUInt64
  | .toBits, a => a.toBits.toUInt64
  | .signed32, a => a.toInt32.toUInt32.toUInt64

/-- The types of source values. -/
inductive Ty where
  | elem (e : Elem)
  | pair (first second : Ty)
  | array (e : Elem)
  | bytes
  | tree (shape : TreeShape)
  | treeHeader (shape : TreeShape) (r : Fin shape.records)
  deriving Repr, DecidableEq, Inhabited

@[match_pattern] abbrev Ty.word : Ty := .elem .word
@[match_pattern] abbrev Ty.bool : Ty := .elem .bool
@[match_pattern] abbrev Ty.float : Ty := .elem .float
@[match_pattern] abbrev Ty.float32 : Ty := .elem .float32

/-- The Lean type of a value. -/
abbrev Ty.denote : Ty → Type
  | .elem e => e.denote
  | .pair a b => a.denote × b.denote
  | .array e => Array e.denote
  | .bytes => LeanExe.Bytes
  | .tree shape => Tree shape
  | .treeHeader shape r => TreeHeader shape r

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
  | .bytes => 2
  | .tree _ | .treeHeader _ _ => 1
  | .pair a b => a.width + b.width

/-- Whether a value needs no heap storage. -/
def Ty.scalar : Ty → Bool
  | .elem _ => true
  | .pair a b => a.scalar && b.scalar
  | .array _ => false
  | .bytes => false
  | .tree _ | .treeHeader _ _ => false

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

def Env.prependRepeat (t : Ty) : (n : Nat) → (Fin n → t.denote) → Env Γ →
    Env (List.replicate n t ++ Γ)
  | 0, _, env => env
  | n + 1, values, env =>
    .cons (values 0) (prependRepeat t n (fun i => values i.succ) env)

/-- The types `ts 0, …, ts (n - 1)`, in order. -/
def tysOfFn : (n : Nat) → (Fin n → Ty) → List Ty
  | 0, _ => []
  | n + 1, ts => ts 0 :: tysOfFn n fun i => ts i.succ

@[simp] theorem tysOfFn_length : (n : Nat) → (ts : Fin n → Ty) → (tysOfFn n ts).length = n
  | 0, _ => rfl
  | n + 1, ts => congrArg (· + 1) (tysOfFn_length n fun i => ts i.succ)

/-- The context of the values `values` of the types `ts`, in order, before `Γ`. -/
def Env.prependFn : (n : Nat) → (ts : Fin n → Ty) → ((i : Fin n) → (ts i).denote) → Env Γ →
    Env (tysOfFn n ts ++ Γ)
  | 0, _, _, env => env
  | n + 1, ts, values, env =>
    .cons (values 0) (prependFn n (fun i => ts i.succ) (fun i => values i.succ) env)

/-- The types of the word fields of record constructor `r`. -/
def TreeShape.wordTy (shape : TreeShape) (r : Fin shape.records) (i : Fin (shape.words r)) : Ty :=
  .elem (shape.elem r i)

/-- The types of the array fields of record constructor `r`. -/
def TreeShape.arrayTy (shape : TreeShape) (r : Fin shape.records) (i : Fin (shape.arrays r)) :
    Ty :=
  .array (shape.arrayElem r i)

/-- The number of variables that a match on record constructor `r` binds: its header, its words,
its children, its arrays, and its buffers. -/
def TreeShape.bindCount (shape : TreeShape) (r : Fin shape.records) : Nat :=
  1 + shape.words r + shape.children r + shape.arrays r + shape.buffers r

def TreeShape.context (shape : TreeShape) (r : Fin shape.records) (Γ : List Ty) : List Ty :=
  .treeHeader shape r :: (tysOfFn (shape.words r) (shape.wordTy r) ++
    (List.replicate (shape.children r) (.tree shape) ++
      (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
      (List.replicate (shape.buffers r) .bytes ++ Γ))))

def Env.treeFields (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape) (env : Env Γ) : Env (shape.context r Γ) :=
  .cons .unit (prependFn (shape.words r) (shape.wordTy r) words
    (prependRepeat (.tree shape) (shape.children r) children
      (prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (prependRepeat .bytes (shape.buffers r) buffers env))))

def Var.ofFin : (Γ : List Ty) → (i : Fin Γ.length) → Var Γ (Γ.get i)
  | _ :: _, ⟨0, _⟩ => .here
  | _ :: Γ, ⟨i + 1, h⟩ => .there (Var.ofFin Γ ⟨i, by simpa using h⟩)

namespace ListFold

abbrev params (e : Elem) (captures : List Ty) : List Ty :=
  .tree listShape :: .elem e :: captures

abbrev context (e : Elem) (captures : List Ty) : List Ty :=
  listShape.context listCell (params e captures)

def nextVar (e : Elem) (captures : List Ty) :
    (i : Fin (params e captures).length) → Var (.elem e :: context e captures) ((params e captures).get i)
  | ⟨0, _⟩ => .there (.there (.there .here))
  | ⟨1, _⟩ => .here
  | ⟨i + 2, h⟩ => .there (.there (.there (.there (.there (.there
      (Var.ofFin captures ⟨i, by simpa [params] using h⟩))))))

def denoteWith {e : Elem} {captures : List Ty}
    (body : Env (context e captures) → e.denote) : Env (params e captures) → e.denote
  | .cons root (.cons init captured) =>
    root.foldlWith (fun cell head tail acc =>
      body (Env.treeFields listShape listCell (fun _ => head)
        (noFields rfl) (noFields rfl) (fun _ => tail) (.cons cell (.cons acc captured)))) init

end ListFold

/-- How a variable holds an array: borrowed, readable while the variable is in scope, or owned,
which its holder must consume. -/
inductive Mode where
  | borrowed | owned
  deriving DecidableEq, Repr, Inhabited

/-- The chosen mode for an array, byte, tree, or tree-header parameter.  Other parameters are borrowed. -/
def Ty.paramMode : Ty → Mode → Mode
  | .array _, m => m
  | .bytes, m => m
  | .tree _, m | .treeHeader _ _, m => m
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
at `unreachable`, which a function that allocates, directly or through a call, does, the modes
chosen for its parameters, and whether its code takes the call depth as a further first argument,
as a recursive function and a function that calls one do.  The call consumes the arrays of its
owned parameters. -/
structure Sig where
  params : List Ty
  result : Ty
  aborts : Bool
  modes : List Mode
  depth : Bool
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
first as variable 1.  `loop count init cond body` is `LeanExe.loop` with a test: starting from
the value of `init`, for each index 0 to `count - 1` it applies `body` to a state that satisfies
`cond` and keeps any other, with the state as variable 0 of `cond`, and the state as variable 0
and the index as variable 1 of `body`.  `cond` does not see the index, so a state that fails it
stays for the remaining indices.  `LeanExe.loop` is the loop whose `cond` is `true`, and
`LeanExe.repeatWhile` is the one whose `body` ignores the index.  `size x` is the number of
elements of the array variable `x` as a word.  `fold x init body` folds over every element of
`x`, with the element, accumulator, and `UInt64` index as variables 0, 1, and 2 of `body`.
The compiled fold uses the represented array's word-sized length.  `get x i` is element `i`
of `x`, or the element type's default value when `i` is not below the size, as Lean's
`x[i.toNat]!` gives.  `leSize x i` compares word variable `i` with the full logical length of `x`.
`build count elem` is `LeanExe.build`: the array of `count` elements whose element `i` is the
value of `elem` with `i` as variable 0.  `set x i v` is `x.set! i.toNat v`: the array of `x` with
element `i` replaced by `v`, or `x` when `i` is not below the size.  `push x v` is `x.push v`,
`append x y` is `x ++ y`, `insertAt x i v` is `LeanExe.insertAt`, the array of `x` with `v`
inserted at position `i`, or `x` when `i` is past the size, and `eraseAt x i` is
`LeanExe.eraseAt`, the array of `x` without element `i`, or `x` when `i` is not below the size.
`float bits` is the float with the bit pattern `bits`, `fbin`, `funary`, and `fcmp` are the
operations and comparisons of floats, and `toFloat` and `toWord` convert between words and
floats.  `mk first second` is the tuple of two elements, and
`proj x p` is the component at path `p` of the tuple variable `x`. -/
inductive Expr (S : List Sig) : List Ty → Ty → Type where
  | word (value : UInt64) : Expr S Γ .word
  | bool (value : Bool) : Expr S Γ .bool
  | treeNil (shape : TreeShape) (h : shape.hasNull = true) : Expr S Γ (.tree shape)
  | treeNode {shape : TreeShape} (r : Fin shape.records)
      (reuse : Option (Var Γ (.treeHeader shape r)))
      (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
      (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
      (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
      (children : Fin (shape.children r) → Expr S Γ (.tree shape)) : Expr S Γ (.tree shape)
  | treeCase {shape : TreeShape} (x : Var Γ (.tree shape))
      (empty : shape.hasNull = true → Expr S Γ t)
      (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t) : Expr S Γ t
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
  | loop (count : Expr S Γ .word) (init : Expr S Γ t) (cond : Expr S (t :: Γ) .bool)
      (body : Expr S (t :: .word :: Γ) t) : Expr S Γ t
  | fold (x : Var Γ (.array e)) (init : Expr S Γ t)
      (body : Expr S (.elem e :: t :: .word :: Γ) t) : Expr S Γ t
  | listFold {e : Elem} {captures : List Ty}
      (args : (i : Fin (ListFold.params e captures).length) →
        Expr S Γ ((ListFold.params e captures).get i))
      (body : Expr S (ListFold.context e captures) (.elem e)) : Expr S Γ (.elem e)
  | size (x : Var Γ (.array e)) : Expr S Γ .word
  | bytesEmpty : Expr S Γ .bytes
  | bytesLiteral (bytes : List UInt8) : Expr S Γ .bytes
  | bytesSize (x : Var Γ .bytes) : Expr S Γ .word
  | bytesGet (x : Var Γ .bytes) (index : Expr S Γ .word) : Expr S Γ .word
  | bytesBuild (count : Expr S Γ .word) (elem : Expr S (.word :: Γ) .word) : Expr S Γ .bytes
  | leSize (x : Var Γ (.array e)) (i : Var Γ .word) : Expr S Γ .bool
  | get (x : Var Γ (.array e)) (i : Expr S Γ .word) : Expr S Γ (.elem e)
  | build (count : Expr S Γ .word) (elem : Expr S (.word :: Γ) (.elem e)) : Expr S Γ (.array e)
  | set (x : Var Γ (.array e)) (i : Expr S Γ .word) (v : Expr S Γ (.elem e)) :
      Expr S Γ (.array e)
  | push (x : Var Γ (.array e)) (v : Expr S Γ (.elem e)) : Expr S Γ (.array e)
  | append (x y : Var Γ (.array e)) : Expr S Γ (.array e)
  | insertAt (x : Var Γ (.array e)) (i : Expr S Γ .word) (v : Expr S Γ (.elem e)) :
      Expr S Γ (.array e)
  | eraseAt (x : Var Γ (.array e)) (i : Expr S Γ .word) : Expr S Γ (.array e)
  | float (bits : UInt64) : Expr S Γ .float
  | float32 (bits : UInt32) : Expr S Γ .float32
  | fbin (op : FBinOp) (left right : Expr S Γ .float) : Expr S Γ .float
  | funary (op : FUnOp) (e : Expr S Γ .float) : Expr S Γ .float
  | fcmp (op : FCmpOp) (left right : Expr S Γ .float) : Expr S Γ .bool
  | toFloat (op : ToFloat) (e : Expr S Γ .word) : Expr S Γ .float
  | toWord (op : ToWord) (e : Expr S Γ .float) : Expr S Γ .word
  | fbin32 (op : FBinOp) (left right : Expr S Γ .float32) : Expr S Γ .float32
  | funary32 (op : F32UnOp) (e : Expr S Γ .float32) : Expr S Γ .float32
  | fcmp32 (op : FCmpOp) (left right : Expr S Γ .float32) : Expr S Γ .bool
  | toFloat32 (op : ToFloat32) (e : Expr S Γ .word) : Expr S Γ .float32
  | toWord32 (op : ToWord32) (e : Expr S Γ .float32) : Expr S Γ .word
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

def Expr.foldStep (x : Var Γ (.array e)) (body : Expr S (.elem e :: t :: .word :: Γ) t) :
    Expr S (t :: .word :: Γ) t :=
  .letE (.get (.there (.there x)) (.var (.there .here))) body

def Expr.foldExpand (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) : Expr S Γ t :=
  .loop (.size x) init (.bool true) (Expr.foldStep x body)

def Elem.zeroExpr {S : List Sig} {Γ : List Ty} : (e : Elem) → Expr S Γ (.elem e)
  | .word => .word 0
  | .bool => .bool false
  | .float => .float 0
  | .float32 => .float32 0
  | .prod a b => .mk a.zeroExpr b.zeroExpr

/-- The family of word expressions of record constructor `r` whose expression `i` is entry `i` of
`exprs` when that entry's element is word `i`'s, and a zero otherwise.  The reflector writes the
words of a construction of a record whose fields hold other elements than `UInt64` in this
form. -/
def TreeShape.exprsOf {S : List Sig} {Γ : List Ty} (shape : TreeShape) (r : Fin shape.records)
    (exprs : List (Σ e : Elem, Expr S Γ (.elem e))) (i : Fin (shape.words r)) :
    Expr S Γ (shape.wordTy r i) :=
  match exprs[i.val]? with
  | some ⟨e, x⟩ =>
    if h : e = shape.elem r i then (h ▸ x : Expr S Γ (.elem (shape.elem r i)))
    else Elem.zeroExpr _
  | none => Elem.zeroExpr _

/-- The array expressions of a construction of record constructor `r`, in the form of
`TreeShape.arraysOf`. -/
def TreeShape.arrayExprsOf {S : List Sig} {Γ : List Ty} (shape : TreeShape)
    (r : Fin shape.records) (exprs : List (Σ e : Elem, Expr S Γ (.array e)))
    (i : Fin (shape.arrays r)) : Expr S Γ (shape.arrayTy r i) :=
  match exprs[i.val]? with
  | some ⟨e, x⟩ =>
    if h : e = shape.arrayElem r i then (h ▸ x : Expr S Γ (.array (shape.arrayElem r i)))
    else .build (.word 0) (shape.arrayElem r i).zeroExpr
  | none => .build (.word 0) (shape.arrayElem r i).zeroExpr

def Expr.insertIdx (x : Var Γ (.array e)) (i : Var Γ .word)
    (value : Expr S Γ (.elem e)) : Expr S Γ (.array e) :=
  .ite (.leSize x i) (.insertAt x (.var i) value) (.build (.word 0) e.zeroExpr)

def Expr.leSizeExpand (x : Var Γ (.array e)) (i : Var Γ .word) : Expr S Γ .bool :=
  .cmp .le (.var i) (.size x)

/-- The value of an expression for the functions `funs` and the values `env` of its
variables. -/
def Expr.denote (funs : Funs S) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Env Γ → t.denote
  | _, _, .word value, _ => value
  | _, _, .bool value, _ => value
  | _, _, .treeNil _ h, _ => .nil h
  | _, _, .treeNode r _ words arrays buffers children, env =>
    .node r (fun i => (words i).denote funs env) (normalFamily fun i => (arrays i).denote funs env)
      (normalFamily fun i => (buffers i).denote funs env) (fun i => (children i).denote funs env)
  | _, _, .treeCase x empty nodes, env =>
    match env.get x with
    | .nil h => (empty h).denote funs env
    | .node r words arrays buffers children =>
      (nodes r).denote funs (env.treeFields _ r words arrays buffers children)
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
  | _, _, .loop count init cond body, env =>
    LeanExe.loop (count.denote funs env) (init.denote funs env)
      fun i acc =>
        bif cond.denote funs (.cons acc env) then body.denote funs (.cons acc (.cons i env))
        else acc
  | _, _, .fold (t := t) x init body, env =>
    ((env.get x).foldl (fun (state : UInt64 × t.denote) value =>
      (state.1 + 1, body.denote funs (.cons value (.cons state.2 (.cons state.1 env)))))
      (0, init.denote funs env)).2
  | _, _, .listFold args body, env =>
    ListFold.denoteWith (body.denote funs) (Env.ofFn fun i => (args i).denote funs env)
  | _, _, .size x, env => (env.get x).size.toUInt64
  | _, _, .bytesEmpty, _ => LeanExe.Bytes.empty
  | _, _, .bytesLiteral bytes, _ => ⟨⟨bytes.toArray⟩⟩
  | _, _, .bytesSize x, env => (env.get x).size
  | _, _, .bytesGet x index, env => (env.get x).get (index.denote funs env)
  | _, _, .bytesBuild count elem, env =>
    LeanExe.Bytes.build (count.denote funs env) fun i => elem.denote funs (.cons i env)
  | _, _, .leSize x i, env => decide ((env.get i).toNat ≤ (env.get x).size)
  | _, _, .get x i, env => (env.get x)[(i.denote funs env).toNat]!
  | _, _, .build count elem, env =>
    LeanExe.build (count.denote funs env) fun i => elem.denote funs (.cons i env)
  | _, _, .set x i v, env => (env.get x).set! (i.denote funs env).toNat (v.denote funs env)
  | _, _, .push x v, env => (env.get x).push (v.denote funs env)
  | _, _, .append x y, env => env.get x ++ env.get y
  | _, _, .insertAt x i v, env =>
    LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env)
  | _, _, .eraseAt x i, env => LeanExe.eraseAt (env.get x) (i.denote funs env)
  | _, _, .float bits, _ => Float.ofBits bits
  | _, _, .float32 bits, _ => Float32.ofBits bits
  | _, _, .fbin op left right, env => op.apply (left.denote funs env) (right.denote funs env)
  | _, _, .funary op e, env => op.apply (e.denote funs env)
  | _, _, .fcmp op left right, env => op.apply (left.denote funs env) (right.denote funs env)
  | _, _, .toFloat op e, env => op.apply (e.denote funs env)
  | _, _, .toWord op e, env => op.apply (e.denote funs env)
  | _, _, .fbin32 op left right, env => op.apply32 (left.denote funs env) (right.denote funs env)
  | _, _, .funary32 op e, env => op.apply (e.denote funs env)
  | _, _, .fcmp32 op left right, env => op.apply32 (left.denote funs env) (right.denote funs env)
  | _, _, .toFloat32 op e, env => op.apply (e.denote funs env)
  | _, _, .toWord32 op e, env => op.apply (e.denote funs env)
  | _, _, .mk first second, env => (first.denote funs env, second.denote funs env)
  | _, _, .proj x p, env => p.get (env.get x)

/-- Whether any of the values `b i` is true. -/
def argsAny : {n : Nat} → ((i : Fin n) → Bool) → Bool
  | 0, _ => false
  | _ + 1, b => b 0 || argsAny fun i => b i.succ

def ListFold.bodyLive (e : Elem) (captures : List Ty) (i : Nat) : Bool :=
  argsAny fun j => (i + 1) == (ListFold.nextVar e captures j).index

/-- Whether the code of an expression may trap: whether it builds, updates, or extends an array,
which may allocate, or calls a function that may trap, whose code takes the call depth, which traps
at the depth limit, that returns arrays, or that owns a parameter, whose argument the call may
copy, since only these allocate. -/
def Expr.aborts : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ | _, _, .float _ | _, _, .float32 _ => false
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right | _, _, .fbin32 _ left right
  | _, _, .fcmp32 _ left right => left.aborts || right.aborts
  | _, _, .toFloat _ e | _, _, .toFloat32 _ e => e.aborts
  | _, _, .toWord _ e | _, _, .toWord32 _ e => e.aborts
  | _, _, .mk first second => first.aborts || second.aborts
  | _, _, .proj _ _ => false
  | _, _, .funary _ e | _, _, .funary32 _ e => e.aborts
  | _, _, .not e => e.aborts
  | _, _, .and left right | _, _, .or left right => left.aborts || right.aborts
  | _, _, .ite c thenE elseE => c.aborts || thenE.aborts || elseE.aborts
  | _, _, .letE value body => value.aborts || body.aborts
  | _, _, .call (g := g) _ args =>
    g.aborts || g.depth || !g.result.scalar ||
      argsAny fun i => (args i).aborts || g.mode i == .owned
  | _, _, .pair first second => first.aborts || second.aborts
  | _, _, .letPair e body => e.aborts || body.aborts
  | _, _, .loop count init cond body => count.aborts || init.aborts || cond.aborts || body.aborts
  | _, _, .fold _ init body => init.aborts || body.aborts
  | _, _, .listFold _ _ => true
  | _, _, .size _ | _, _, .leSize _ _ => false
  | _, _, .bytesEmpty | _, _, .bytesLiteral _ => true
  | _, _, .bytesSize _ => false
  | _, _, .bytesGet _ index => index.aborts
  | _, _, .bytesBuild _ _ => true
  | _, _, .get _ i => i.aborts
  | _, _, .build _ _ | _, _, .set _ _ _ | _, _, .push _ _ | _, _, .append _ _
  | _, _, .insertAt _ _ _ | _, _, .eraseAt _ _ => true
  | _, _, .treeNil _ _ | _, _, .treeNode _ _ _ _ _ _ | _, _, .treeCase _ _ _ => true

/-- Whether an expression calls a function whose code takes the call depth. -/
def Expr.depthCalls : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Bool
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ | _, _, .float _ | _, _, .float32 _ => false
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right | _, _, .fbin32 _ left right
  | _, _, .fcmp32 _ left right => left.depthCalls || right.depthCalls
  | _, _, .toFloat _ e | _, _, .toFloat32 _ e => e.depthCalls
  | _, _, .toWord _ e | _, _, .toWord32 _ e => e.depthCalls
  | _, _, .mk first second => first.depthCalls || second.depthCalls
  | _, _, .proj _ _ => false
  | _, _, .funary _ e | _, _, .funary32 _ e => e.depthCalls
  | _, _, .not e => e.depthCalls
  | _, _, .and left right | _, _, .or left right => left.depthCalls || right.depthCalls
  | _, _, .ite c thenE elseE => c.depthCalls || thenE.depthCalls || elseE.depthCalls
  | _, _, .letE value body => value.depthCalls || body.depthCalls
  | _, _, .call (g := g) _ args => g.depth || argsAny fun i => (args i).depthCalls
  | _, _, .pair first second => first.depthCalls || second.depthCalls
  | _, _, .letPair e body => e.depthCalls || body.depthCalls
  | _, _, .loop count init cond body =>
    count.depthCalls || init.depthCalls || cond.depthCalls || body.depthCalls
  | _, _, .fold _ init body => init.depthCalls || body.depthCalls
  | _, _, .listFold args body => (argsAny fun i => (args i).depthCalls) || body.depthCalls
  | _, _, .size _ | _, _, .leSize _ _ => false
  | _, _, .bytesEmpty | _, _, .bytesLiteral _ | _, _, .bytesSize _ => false
  | _, _, .bytesGet _ index => index.depthCalls
  | _, _, .bytesBuild count elem => count.depthCalls || elem.depthCalls
  | _, _, .get _ i => i.depthCalls
  | _, _, .build count elem => count.depthCalls || elem.depthCalls
  | _, _, .set _ i v | _, _, .insertAt _ i v => i.depthCalls || v.depthCalls
  | _, _, .eraseAt _ i => i.depthCalls
  | _, _, .push _ v => v.depthCalls
  | _, _, .append _ _ => false
  | _, _, .treeNil _ _ => false
  | _, _, .treeNode _ _ words arrays buffers children =>
    (argsAny fun i => (words i).depthCalls) || (argsAny fun i => (children i).depthCalls) ||
      (argsAny fun i => (arrays i).depthCalls) || argsAny fun i => (buffers i).depthCalls
  | _, _, .treeCase (shape := shape) _ empty nodes =>
    (if h : shape.hasNull = true then (empty h).depthCalls else false) ||
      argsAny fun r => (nodes r).depthCalls

def optionVarUses (value : Option (Var Γ t)) (i : Nat) : Bool :=
  match value with
  | none => false
  | some x => i == x.index

def optionVarMask (value : Option (Var Γ t)) : Nat :=
  match value with
  | none => 0
  | some x => 1 <<< x.index

/-- The variables that an expression reads, by index. -/
def Expr.uses : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat → Bool
  | _, _, .word _, _ | _, _, .bool _, _ | _, _, .float _, _ | _, _, .float32 _, _ => false
  | _, _, .var x, i => i == x.index
  | _, _, .bin _ left right, i | _, _, .cmp _ left right, i | _, _, .fbin _ left right, i
  | _, _, .fcmp _ left right, i | _, _, .fbin32 _ left right, i
  | _, _, .fcmp32 _ left right, i => left.uses i || right.uses i
  | _, _, .toFloat _ e, i | _, _, .toFloat32 _ e, i => e.uses i
  | _, _, .toWord _ e, i | _, _, .toWord32 _ e, i => e.uses i
  | _, _, .mk first second, i => first.uses i || second.uses i
  | _, _, .proj x _, i => i == x.index
  | _, _, .funary _ e, i | _, _, .funary32 _ e, i => e.uses i
  | _, _, .not e, i => e.uses i
  | _, _, .and left right, i | _, _, .or left right, i => left.uses i || right.uses i
  | _, _, .ite c thenE elseE, i => c.uses i || thenE.uses i || elseE.uses i
  | _, _, .letE value body, i => value.uses i || body.uses (i + 1)
  | _, _, .call _ args, i => argsAny fun j => (args j).uses i
  | _, _, .pair first second, i => first.uses i || second.uses i
  | _, _, .letPair e body, i => e.uses i || body.uses (i + 2)
  | _, _, .loop count init cond body, i =>
    count.uses i || init.uses i || cond.uses (i + 1) || body.uses (i + 2)
  | _, _, .fold x init body, i =>
    (i == x.index) || init.uses i || body.uses (i + 3)
  | _, _, .listFold args _, i => argsAny fun j => (args j).uses i
  | _, _, .size x, i => i == x.index
  | _, _, .bytesEmpty, _ | _, _, .bytesLiteral _, _ => false
  | _, _, .bytesSize x, i => i == x.index
  | _, _, .bytesGet x index, i => i == x.index || index.uses i
  | _, _, .bytesBuild count elem, i => count.uses i || elem.uses (i + 1)
  | _, _, .leSize x k, i => i == k.index || i == x.index
  | _, _, .get x k, i => i == x.index || k.uses i
  | _, _, .build count elem, i => count.uses i || elem.uses (i + 1)
  | _, _, .set x k v, i | _, _, .insertAt x k v, i => i == x.index || k.uses i || v.uses i
  | _, _, .eraseAt x k, i => i == x.index || k.uses i
  | _, _, .push x v, i => i == x.index || v.uses i
  | _, _, .append x y, i => i == x.index || i == y.index
  | _, _, .treeNil _ _, _ => false
  | _, _, .treeNode _ reuse words arrays buffers children, i =>
    optionVarUses reuse i || (argsAny fun j => (words j).uses i) ||
      (argsAny fun j => (children j).uses i) || (argsAny fun j => (arrays j).uses i) ||
      argsAny fun j => (buffers j).uses i
  | _, _, .treeCase (shape := shape) x empty nodes, i =>
    (i == x.index) || (if h : shape.hasNull = true then (empty h).uses i else false) ||
      argsAny fun r => (nodes r).uses (i + shape.bindCount r)

/-- The union of the bitmasks `b i`, as `argsAny` is the disjunction of the values. -/
def argsMask : {n : Nat} → ((i : Fin n) → Nat) → Nat
  | 0, _ => 0
  | _ + 1, b => b 0 ||| argsMask fun i => b i.succ

/-- The variables that an expression reads, as a bitmask whose bit `i` is set when it reads
variable `i`: `Expr.uses` as data.  The code generator asks whether many variables are read by
the same subexpression, and the kernel evaluates the code generator in every program's byte
theorem, so it computes the mask of a subexpression once instead of walking the subexpression
for each variable. -/
def Expr.useMask : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat
  | _, _, .word _ | _, _, .bool _ | _, _, .float _ | _, _, .float32 _ => 0
  | _, _, .var x => 1 <<< x.index
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right | _, _, .fbin32 _ left right
  | _, _, .fcmp32 _ left right => left.useMask ||| right.useMask
  | _, _, .toFloat _ e | _, _, .toFloat32 _ e => e.useMask
  | _, _, .toWord _ e | _, _, .toWord32 _ e => e.useMask
  | _, _, .mk first second => first.useMask ||| second.useMask
  | _, _, .proj x _ => 1 <<< x.index
  | _, _, .funary _ e | _, _, .funary32 _ e => e.useMask
  | _, _, .not e => e.useMask
  | _, _, .and left right | _, _, .or left right => left.useMask ||| right.useMask
  | _, _, .ite c thenE elseE => c.useMask ||| thenE.useMask ||| elseE.useMask
  | _, _, .letE value body => value.useMask ||| body.useMask >>> 1
  | _, _, .call _ args => argsMask fun j => (args j).useMask
  | _, _, .pair first second => first.useMask ||| second.useMask
  | _, _, .letPair e body => e.useMask ||| body.useMask >>> 2
  | _, _, .loop count init cond body =>
    count.useMask ||| init.useMask ||| cond.useMask >>> 1 ||| body.useMask >>> 2
  | _, _, .fold x init body =>
    (1 <<< x.index) ||| init.useMask ||| body.useMask >>> 3
  | _, _, .listFold args _ => argsMask fun i => (args i).useMask
  | _, _, .size x => 1 <<< x.index
  | _, _, .bytesEmpty | _, _, .bytesLiteral _ => 0
  | _, _, .bytesSize x => 1 <<< x.index
  | _, _, .bytesGet x index => 1 <<< x.index ||| index.useMask
  | _, _, .bytesBuild count elem => count.useMask ||| elem.useMask >>> 1
  | _, _, .leSize x i => (1 <<< i.index) ||| (1 <<< x.index)
  | _, _, .get x k => 1 <<< x.index ||| k.useMask
  | _, _, .build count elem => count.useMask ||| elem.useMask >>> 1
  | _, _, .set x k v | _, _, .insertAt x k v => 1 <<< x.index ||| k.useMask ||| v.useMask
  | _, _, .eraseAt x k => 1 <<< x.index ||| k.useMask
  | _, _, .push x v => 1 <<< x.index ||| v.useMask
  | _, _, .append x y => 1 <<< x.index ||| 1 <<< y.index
  | _, _, .treeNil _ _ => 0
  | _, _, .treeNode _ reuse words arrays buffers children =>
    optionVarMask reuse ||| (argsMask fun j => (words j).useMask) |||
      (argsMask fun j => (children j).useMask) ||| (argsMask fun j => (arrays j).useMask) |||
      argsMask fun j => (buffers j).useMask
  | _, _, .treeCase (shape := shape) x empty nodes =>
    (1 <<< x.index) ||| (if h : shape.hasNull = true then (empty h).useMask else 0) |||
      argsMask fun r => (nodes r).useMask >>> shape.bindCount r

/-- `Expr.uses` read from `Expr.useMask`, which the code generator calls. -/
def Expr.usesFast (e : Expr S Γ t) (i : Nat) : Bool := e.useMask.testBit i

theorem testBit_one_shiftLeft (k i : Nat) : (1 <<< k).testBit i = (i == k) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : k = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem argsMask_testBit : {n : Nat} → (b : (i : Fin n) → Nat) → (i : Nat) →
    (argsMask b).testBit i = argsAny fun j => (b j).testBit i
  | 0, _, _ => by simp [argsMask, argsAny]
  | _ + 1, b, i => by
    simp only [argsMask, argsAny, Nat.testBit_or, argsMask_testBit (fun j => b j.succ) i]

theorem optionVarMask_testBit (value : Option (Var Γ t)) (i : Nat) :
    (optionVarMask value).testBit i = optionVarUses value i := by
  cases value <;> simp [optionVarMask, optionVarUses, testBit_one_shiftLeft,
    -Nat.testBit_shiftLeft]

theorem Expr.usesFast_eq {Γ : List Ty} {t : Ty} (e : Expr S Γ t) (i : Nat) :
    e.usesFast i = e.uses i := by
  unfold Expr.usesFast
  induction e generalizing i with
  | word | bool | float | float32 | treeNil | bytesEmpty | bytesLiteral =>
    simp [Expr.useMask, Expr.uses]
  | var x | proj x _ | size x | bytesSize x =>
    simp [Expr.useMask, Expr.uses, testBit_one_shiftLeft, -Nat.testBit_shiftLeft]
  | call f args ih =>
    simp only [Expr.useMask, Expr.uses, argsMask_testBit]
    congr 1
    funext j
    exact ih j i
  | listFold args body ihArgs _ =>
    simp only [Expr.useMask, Expr.uses, argsMask_testBit]
    congr 1
    funext j
    exact ihArgs j i
  | treeNode r reuse words arrays buffers children wordIh arrayIh bufferIh childIh =>
    simp_all only [Expr.useMask, Expr.uses, Nat.testBit_or, argsMask_testBit,
      optionVarMask_testBit]
  | treeCase x empty nodes emptyIh nodesIh =>
    simp only [Expr.useMask, Expr.uses, Nat.testBit_or, argsMask_testBit, Nat.testBit_shiftRight,
      testBit_one_shiftLeft, nodesIh, Nat.add_comm]
    split <;> simp_all
  | _ =>
    simp_all [Expr.useMask, Expr.uses, Nat.testBit_or, Nat.testBit_shiftRight,
      testBit_one_shiftLeft, Nat.add_comm, -Nat.testBit_shiftLeft]

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
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ | _, _, .size _ | _, _, .float _ | _, _, .float32 _
  | _, _, .leSize _ _ => true
  | _, _, .bin _ left right | _, _, .cmp _ left right | _, _, .fbin _ left right
  | _, _, .fcmp _ left right | _, _, .fbin32 _ left right
  | _, _, .fcmp32 _ left right => left.placeArgs && right.placeArgs
  | _, _, .toFloat _ e | _, _, .toFloat32 _ e => e.placeArgs
  | _, _, .toWord _ e | _, _, .toWord32 _ e => e.placeArgs
  | _, _, .mk first second => first.placeArgs && second.placeArgs
  | _, _, .proj _ _ => true
  | _, _, .funary _ e | _, _, .funary32 _ e => e.placeArgs
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
  | _, _, .loop count init cond body =>
    count.placeArgs && init.placeArgs && cond.placeArgs && body.placeArgs
  | _, _, .fold _ init body => init.placeArgs && body.placeArgs
  | _, _, .listFold (e := e) (captures := captures) args body =>
    !(argsAny fun i => !((ListFold.params e captures).get i).scalar && !(args i).isPlace) &&
      !(argsAny fun i => !(args i).placeArgs) && body.placeArgs
  | _, _, .get _ i => i.placeArgs
  | _, _, .bytesEmpty | _, _, .bytesLiteral _ | _, _, .bytesSize _ => true
  | _, _, .bytesGet _ index => index.placeArgs
  | _, _, .bytesBuild count elem => count.placeArgs && elem.placeArgs
  | _, _, .build count elem => count.placeArgs && elem.placeArgs
  | _, _, .set _ i v | _, _, .insertAt _ i v => i.placeArgs && v.placeArgs
  | _, _, .eraseAt _ i => i.placeArgs
  | _, _, .push _ v => v.placeArgs
  | _, _, .append _ _ => true
  | _, _, .treeNil _ _ => true
  | _, _, .treeNode _ _ words arrays buffers children =>
    !(argsAny fun i => !(words i).placeArgs) && !(argsAny fun i => !(children i).placeArgs) &&
      !(argsAny fun i => !(arrays i).placeArgs) && !(argsAny fun i => !(buffers i).placeArgs)
  | _, _, .treeCase (shape := shape) _ empty nodes =>
    (if h : shape.hasNull = true then (empty h).placeArgs else true) &&
      !(argsAny fun r => !(nodes r).placeArgs)

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

/-- Whether the function's code takes the call depth: whether its body calls a function whose
code does. -/
def Func.depth (func : Func S) : Bool := func.body.depthCalls

/-- The Lean function that `func` means, given the Lean functions that it calls. -/
def Func.denote (func : Func S) (funs : Funs S) (args : Env func.params) : func.result.denote :=
  func.body.denote funs args

/-- The signature of a function of a program. -/
def Func.sig (func : Func S) : Sig :=
  ⟨func.params, func.result, func.aborts, func.modes, func.depth⟩

/-- A recursive function: its body may call the functions `S` and, as the function before them,
itself.  Its code takes the call depth and may trap at `unreachable` when the depth reaches the
limit, so its signature, `sig`, has both flags. -/
structure RecFunc (S : List Sig) where
  name : String
  params : List Ty
  result : Ty
  modes : List Mode
  body : Expr (⟨params, result, true, modes, true⟩ :: S) params result
  placeArgs : body.placeArgs = true

def RecFunc.sig (func : RecFunc S) : Sig := ⟨func.params, func.result, true, func.modes, true⟩

/-- The mode that holds both of two values' arrays: owned when either is owned. -/
def Mode.join : Mode → Mode → Mode
  | .borrowed, .borrowed => .borrowed
  | _, _ => .owned

def TreeShape.modes (shape : TreeShape) (r : Fin shape.records) (mode : Mode)
    (modes : List Mode) : List Mode :=
  mode :: (List.replicate (shape.words r) .borrowed ++ (List.replicate (shape.children r) mode ++
    (List.replicate (shape.arrays r) mode ++ (List.replicate (shape.buffers r) mode ++ modes))))

/-- The join of the modes `m r` over the record constructors, from `init`. -/
def recordsJoin : {n : Nat} → (Fin n → Mode) → Mode → Mode
  | 0, _, init => init
  | _ + 1, m, init => (m 0).join (recordsJoin (fun r => m r.succ) init)

theorem recordsJoin_init : ∀ {n : Nat} (modes : Fin n → Mode) (init : Mode),
    init = .owned → recordsJoin modes init = .owned
  | 0, _, _, h => h
  | _ + 1, modes, init, h => by
    simp only [recordsJoin]
    rw [recordsJoin_init (fun r => modes r.succ) init h]
    cases modes 0 <;> rfl

theorem recordsJoin_at : ∀ {n : Nat} (modes : Fin n → Mode) (init : Mode) (i : Fin n),
    modes i = .owned → recordsJoin modes init = .owned
  | _ + 1, modes, init, i, h => by
    simp only [recordsJoin]
    cases i using Fin.cases with
    | zero => rw [h]; rfl
    | succ i =>
      rw [recordsJoin_at (fun r => modes r.succ) init i h]
      cases modes 0 <;> rfl

/-- The mode of an expression's value, given the modes of the variables: owned when it holds
arrays that its holder must consume, which a call's result, a built, updated, or extended array, a
moved or copied variable, and a join of an owned value do. -/
def Expr.mode (modes : List Mode) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Mode
  | _, _, .var x => modes.getD x.index .borrowed
  | _, _, .ite _ thenE elseE => (thenE.mode modes).join (elseE.mode modes)
  | _, _, .letE value body => body.mode (value.mode modes :: modes)
  | _, _, .call (g := g) _ _ => if g.result.scalar then .borrowed else .owned
  | _, _, .build _ _ | _, _, .set _ _ _ | _, _, .push _ _ | _, _, .append _ _
  | _, _, .insertAt _ _ _ | _, _, .eraseAt _ _ => .owned
  | _, _, .pair first second => (first.mode modes).join (second.mode modes)
  | _, _, .letPair e body => body.mode (e.mode modes :: e.mode modes :: modes)
  | _, _, .loop _ init _ body =>
    (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
  | _, _, .fold _ init body =>
    (init.mode modes).join (body.mode (.borrowed :: .borrowed :: .borrowed :: modes))
  | _, _, .treeNil _ _ | _, _, .treeNode _ _ _ _ _ _ => .owned
  | _, _, .bytesEmpty | _, _, .bytesLiteral _ | _, _, .bytesBuild _ _ => .owned
  | _, _, .treeCase (shape := shape) x empty nodes =>
    recordsJoin (fun r => (nodes r).mode (shape.modes r (modes.getD x.index .borrowed) modes))
      (if h : shape.hasNull = true then (empty h).mode modes else .borrowed)
  | _, _, _ => .borrowed

inductive TailBody (S : List Sig) (params : List Ty) (result : Ty) : List Ty → Type where
  | ret (value : Expr S Γ result) : TailBody S params result Γ
  | next (args : (i : Fin params.length) → Expr S Γ (params.get i)) :
      TailBody S params result Γ
  | ite (cond : Expr S Γ .bool) (yes no : TailBody S params result Γ) :
      TailBody S params result Γ
  | letE (value : Expr S Γ t) (body : TailBody S params result (t :: Γ)) :
      TailBody S params result Γ
  | letPair (value : Expr S Γ (.pair s t)) (body : TailBody S params result (t :: s :: Γ)) :
      TailBody S params result Γ
  | treeCase {shape : TreeShape} (x : Var Γ (.tree shape))
      (empty : shape.hasNull = true → TailBody S params result Γ)
      (nodes : (r : Fin shape.records) → TailBody S params result (shape.context r Γ)) :
      TailBody S params result Γ

def TailBody.denote (funs : Funs S) : {Γ : List Ty} → TailBody S params result Γ →
    Env Γ → Sum (Env params) result.denote
  | _, .ret value, env => .inr (value.denote funs env)
  | _, .next args, env => .inl (Env.ofFn fun i => (args i).denote funs env)
  | _, .ite cond yes no, env =>
    if cond.denote funs env then yes.denote funs env else no.denote funs env
  | _, .letE value body, env => body.denote funs (.cons (value.denote funs env) env)
  | _, .letPair value body, env =>
    let pair := value.denote funs env
    body.denote funs (.cons pair.2 (.cons pair.1 env))
  | _, .treeCase x empty nodes, env =>
    match env.get x with
    | .nil h => (empty h).denote funs env
    | .node r words arrays buffers children =>
      (nodes r).denote funs (Env.treeFields _ r words arrays buffers children env)

def TailBody.uses : {Γ : List Ty} → TailBody S params result Γ → Nat → Bool
  | _, .ret value, i => value.uses i
  | _, .next args, i => argsAny fun j => (args j).uses i
  | _, .ite cond yes no, i => cond.uses i || yes.uses i || no.uses i
  | _, .letE value body, i => value.uses i || body.uses (i + 1)
  | _, .letPair value body, i => value.uses i || body.uses (i + 2)
  | _, .treeCase (shape := shape) x empty nodes, i =>
    (i == x.index) || (if h : shape.hasNull = true then (empty h).uses i else false) ||
      argsAny fun r => (nodes r).uses (i + shape.bindCount r)

def TailBody.useMask : {Γ : List Ty} → TailBody S params result Γ → Nat
  | _, .ret value => value.useMask
  | _, .next args => argsMask fun j => (args j).useMask
  | _, .ite cond yes no => cond.useMask ||| yes.useMask ||| no.useMask
  | _, .letE value body => value.useMask ||| body.useMask >>> 1
  | _, .letPair value body => value.useMask ||| body.useMask >>> 2
  | _, .treeCase (shape := shape) x empty nodes =>
    (1 <<< x.index) ||| (if h : shape.hasNull = true then (empty h).useMask else 0) |||
      argsMask fun r => (nodes r).useMask >>> shape.bindCount r

def TailBody.usesFast (body : TailBody S params result Γ) (i : Nat) : Bool :=
  body.useMask.testBit i

def TailBody.depthCalls : {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.depthCalls
  | _, .next args => argsAny fun i => (args i).depthCalls
  | _, .ite cond yes no => cond.depthCalls || yes.depthCalls || no.depthCalls
  | _, .letE value body | _, .letPair value body => value.depthCalls || body.depthCalls
  | _, .treeCase (shape := shape) _ empty nodes =>
    (if h : shape.hasNull = true then (empty h).depthCalls else false) ||
      argsAny fun r => (nodes r).depthCalls

def TailBody.aborts : {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.aborts
  | _, .next args => argsAny fun i => (args i).aborts
  | _, .ite cond yes no => cond.aborts || yes.aborts || no.aborts
  | _, .letE value body | _, .letPair value body => value.aborts || body.aborts
  | _, .treeCase _ _ _ => true

def TailBody.placeArgs (targetModes : List Mode) (modes : List Mode) :
    {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.placeArgs
  | _, .next args =>
    !(argsAny fun i => !(args i).placeArgs) &&
      !(argsAny fun i =>
        !(params.get i).scalar &&
          if paramMode params targetModes i == .owned then (args i).varIndex?.isNone
          else !(args i).isPlace || (args i).mode modes != .borrowed)
  | _, .ite cond yes no =>
    cond.placeArgs && yes.placeArgs targetModes modes && no.placeArgs targetModes modes
  | _, .letE value body =>
    value.placeArgs && body.placeArgs targetModes (value.mode modes :: modes)
  | _, .letPair value body =>
    value.placeArgs && body.placeArgs targetModes (value.mode modes :: value.mode modes :: modes)
  | _, .treeCase (shape := shape) x empty nodes =>
    (if h : shape.hasNull = true then (empty h).placeArgs targetModes modes else true) &&
      !(argsAny fun r =>
        !(nodes r).placeArgs targetModes (shape.modes r (modes.getD x.index .borrowed) modes))

structure TailFunc (S : List Sig) where
  name : String
  params : List Ty
  result : Ty
  modes : List Mode
  body : TailBody S params result params
  placeArgs : body.placeArgs modes (paramModes params modes) = true
  rank : Funs S → Env params → Nat

def TailFunc.Decreases (func : TailFunc S) (funs : Funs S) : Prop :=
  ∀ state next, func.body.denote funs state = .inl next → func.rank funs next < func.rank funs state

def TailFunc.depth (func : TailFunc S) : Bool := func.body.depthCalls

def TailFunc.aborts (func : TailFunc S) : Bool :=
  func.body.aborts || !func.result.scalar || (paramModes func.params func.modes).any (· == .owned)

def TailFunc.sig (func : TailFunc S) : Sig :=
  ⟨func.params, func.result, func.aborts, func.modes, func.depth⟩

/-- A program: functions in which each may call the functions after it in the list, which come
before it in the module, and a recursive function itself. -/
inductive Prog : List Sig → Type where
  | nil : Prog []
  | cons (f : Func S) (rest : Prog S) : Prog (f.sig :: S)
  | consRec (f : RecFunc S) (rest : Prog S) : Prog (f.sig :: S)
  | consTail (f : TailFunc S) (rest : Prog S) : Prog (f.sig :: S)

instance Ty.instInhabited : (t : Ty) → Inhabited t.denote
  | .elem e => e.instInhabited
  | .pair a b => ⟨(@default _ (Ty.instInhabited a), @default _ (Ty.instInhabited b))⟩
  | .array _ => ⟨#[]⟩
  | .bytes => inferInstanceAs (Inhabited LeanExe.Bytes)
  | .tree shape => ⟨Tree.default shape⟩
  | .treeHeader _ _ => ⟨.unit⟩

/-- Whether a program has no recursive function. -/
def Prog.recFree : {S : List Sig} → Prog S → Bool
  | _, .nil => true
  | _, .cons _ rest => rest.recFree
  | _, .consRec _ _ => false
  | _, .consTail _ _ => false

/-- The Lean functions that a program's functions mean, for a program without recursion.  A
recursive function has no meaning by its body alone, and gets the default value here; its meaning
is a solution of its equation, which `Prog.Meaning` states. -/
def Prog.funs : {S : List Sig} → Prog S → Funs S
  | _, .nil => .nil
  | _, .cons f rest => .cons (f.denote rest.funs) rest.funs
  | _, .consRec f rest => .cons (fun _ => @default _ (Ty.instInhabited f.result)) rest.funs
  | _, .consTail f rest => .cons (fun _ => @default _ (Ty.instInhabited f.result)) rest.funs

/-- `funs` are the Lean functions that a program's functions mean: a function's meaning is its
body's at the meanings of the functions after it, and a recursive function's meaning is any `M`
whose value is its body's at `M` and those meanings, which the reflector gives as the Lean
definition. -/
inductive Prog.Meaning : {S : List Sig} → Prog S → Funs S → Prop
  | nil : Prog.Meaning .nil .nil
  | cons {S : List Sig} {f : Func S} {rest : Prog S} {funs : Funs S} :
    Prog.Meaning rest funs → Prog.Meaning (Prog.cons f rest) (.cons (f.denote funs) funs)
  | consRec {S : List Sig} {f : RecFunc S} {rest : Prog S} {funs : Funs S}
    (M : Env f.params → f.result.denote) : Prog.Meaning rest funs →
    (∀ env, M env = f.body.denote (.cons (g := f.sig) M funs) env) →
    Prog.Meaning (Prog.consRec f rest) (.cons M funs)
  | consTail {S : List Sig} {f : TailFunc S} {rest : Prog S} {funs : Funs S}
    (M : Env f.params → f.result.denote) : Prog.Meaning rest funs → f.Decreases funs →
    (∀ env, M env = (f.body.denote funs env).elim M id) →
    Prog.Meaning (Prog.consTail f rest) (.cons M funs)

theorem Prog.meaning_funs : {S : List Sig} → (prog : Prog S) → prog.recFree = true →
    prog.Meaning prog.funs
  | _, .nil, _ => .nil
  | _, .cons _ rest, h => .cons (rest.meaning_funs h)
  | _, .consRec _ _, h => nomatch h
  | _, .consTail _ _, h => nomatch h

theorem Prog.get_here {S : List Sig} (f : Func S) (rest : Prog S) (env : Env f.params) :
    (Prog.cons f rest).funs.get .here env = f.denote rest.funs env := rfl

theorem Prog.get_there {S : List Sig} {g : Sig} (f : Func S) (rest : Prog S) (v : FVar S g)
    (env : Env g.params) : (Prog.cons f rest).funs.get (.there v) env = rest.funs.get v env :=
  rfl

theorem Funs.get_here {S : List Sig} {g : Sig} (F : Env g.params → g.result.denote)
    (rest : Funs S) (env : Env g.params) : (Funs.cons F rest).get .here env = F env :=
  rfl

theorem Funs.get_there {S : List Sig} {g h : Sig} (F : Env h.params → h.result.denote)
    (rest : Funs S) (v : FVar S g) (env : Env g.params) :
    (Funs.cons F rest).get (.there v) env = rest.get v env :=
  rfl

end Verified
