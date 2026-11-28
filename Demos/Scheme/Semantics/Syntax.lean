module

public import Demos.Scheme.Semantics.Datum
public import Demos.Scheme.Semantics.Numeric

@[expose] public section

/-! The core syntax of the reference semantics: the abstract syntax of §7.2.1, into which the
expander rewrites every essential form by the rules of §7.3, and the standard procedures that the
profile implements.  A variable is an identifier of the source or a temporary of a rewrite rule,
which no identifier can denote.  A constant is a datum, the location of an allocated literal,
§7.3's `<undefined>`, an unspecified value, or a standard procedure that a rule names, such as
§7.3's `<memv>`. -/

namespace Demos.Scheme.Semantics

/-- A variable: an identifier, or a temporary of a rewrite rule. -/
inductive Var where
  | id (s : Sym)
  | temp (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The standard procedures of the profile.  `cxr path` is the composition of `car`s and `cdr`s
that `path` lists in the order of application, `true` for `car`, such as `[false, true]` for
`cadr`. -/
inductive Prim where
  | not | isBoolean
  | eq | eqv
  | isPair | cons | car | cdr | setCar | setCdr | cxr (path : List Bool)
  | isNull | isList | list | length | append | reverse | listRef
  | memq | memv | assq | assv
  | num (op : Numeric.Op)
  | isProcedure | apply | map | forEach | callcc
  | isVector | listToVector
  deriving DecidableEq, Repr, Inhabited

/-- The essential arity of each procedure (§6). -/
def Prim.arity : Prim → Numeric.Arity
  | .eq | .eqv | .cons | .setCar | .setCdr | .listRef | .memq | .memv | .assq | .assv | .apply =>
    .exact 2
  | .list | .append => .atLeast 0
  | .num op => op.arity
  | .map | .forEach => .atLeast 2
  | _ => .exact 1

/-- The sequences of `n` letters of `a` and `d`, with `true` for `a`. -/
def letterSeqs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (letterSeqs n).flatMap fun s => [true :: s, false :: s]

/-- The compositions `caar` to `cddddr` (§6.3), with their paths: the letters between `c` and `r`
name the operations, and the last letter's operation applies first. -/
def cxrNames : List (Sym × List Bool) :=
  ([2, 3, 4].flatMap letterSeqs).map fun letters =>
    (99 :: letters.map (fun b => if b then (97 : UInt8) else 100) ++ [114], letters.reverse)

/-- The top-level names of the standard procedures, in the order of their identity tags.  The
names `call-with-current-continuation` and `call/cc` denote the same procedure. -/
def primNames : List (Sym × Prim) :=
  [("not", .not), ("boolean?", .isBoolean), ("eq?", .eq), ("eqv?", .eqv), ("pair?", .isPair),
    ("cons", .cons), ("car", .car), ("cdr", .cdr), ("set-car!", .setCar),
    ("set-cdr!", .setCdr)].map (fun (n, p) => (bytes n, p)) ++
  (cxrNames.map fun (n, path) => (n, .cxr path)) ++
  ([("null?", .isNull), ("list?", .isList), ("list", .list), ("length", .length),
    ("append", .append), ("reverse", .reverse), ("list-ref", .listRef), ("memq", .memq),
    ("memv", .memv), ("assq", .assq), ("assv", .assv),
    ("number?", .num .isNumber), ("complex?", .num .isComplex), ("real?", .num .isReal),
    ("rational?", .num .isRational), ("integer?", .num .isInteger), ("exact?", .num .isExact),
    ("inexact?", .num .isInexact), ("=", .num .eq), ("<", .num .lt), (">", .num .gt),
    ("<=", .num .le), (">=", .num .ge), ("zero?", .num .isZero),
    ("positive?", .num .isPositive), ("negative?", .num .isNegative), ("odd?", .num .isOdd),
    ("even?", .num .isEven), ("max", .num .max), ("min", .num .min), ("+", .num .add),
    ("*", .num .mul), ("-", .num .sub), ("/", .num .div), ("abs", .num .abs),
    ("quotient", .num .quotient), ("remainder", .num .remainder), ("modulo", .num .modulo),
    ("gcd", .num .gcd), ("lcm", .num .lcm), ("floor", .num .floor),
    ("ceiling", .num .ceiling), ("truncate", .num .truncate), ("round", .num .round),
    ("procedure?", .isProcedure), ("apply", .apply), ("map", .map), ("for-each", .forEach),
    ("call-with-current-continuation", .callcc), ("call/cc", .callcc),
    ("vector?", .isVector), ("list->vector", .listToVector)].map fun (n, p) => (bytes n, p))

/-- The syntactic keywords of §2.1, which the profile reserves. -/
def keywords : List Sym :=
  ["=>", "and", "begin", "case", "cond", "define", "delay", "do", "else", "if", "lambda", "let",
    "let*", "letrec", "or", "quasiquote", "quote", "set!", "unquote", "unquote-splicing"].map
    bytes

def isKeyword (s : Sym) : Bool := keywords.contains s

/-- A constant (§7.2.1's `K`).  `datum d` holds an atom, or a compound datum before the
allocation of literals replaces it by `lit l`, the location that holds its object. -/
inductive Const where
  | datum (d : Datum)
  | lit (l : Nat)
  | undefined
  | unspecified
  | prim (p : Prim)
  deriving Inhabited

/-- Expressions: the abstract syntax of §7.2.1.  `lam fixed rest body last` is
`(lambda (I*) Γ* E0)` when `rest` is `none` and `(lambda (I* . I) Γ* E0)` otherwise, with the
commands `body` and the last expression `last`. -/
inductive Expr where
  | const (k : Const)
  | var (x : Var)
  | app (f : Expr) (args : List Expr)
  | lam (fixed : List Var) (rest : Option Var) (body : List Expr) (last : Expr)
  | ite (c t e : Expr)
  | set (x : Var) (e : Expr)
  deriving Inhabited

/-- A top-level form of a program (§5.1): an expression or a definition. -/
inductive TopForm where
  | expr (e : Expr)
  | define (x : Sym) (e : Expr)
  deriving Inhabited

end Demos.Scheme.Semantics
