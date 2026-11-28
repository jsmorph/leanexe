module

public import Demos.Scheme.Machine.Text

@[expose] public section

/-! The code of the executable interpreter: the core syntax of §7.2.1 as objects of the kind
`K_CODE` in the arena, which the expander builds and the evaluator reads.  A variable of a
`lambda` is a lexical address, its position in the chain of locations of the environment, and a
top-level variable is its symbol.

| Subkind | Fields | Core syntax |
|---|---|---|
| `C_CONST` | a: the value | a constant |
| `C_LREF` | a: the position | a variable of a `lambda` |
| `C_GREF` | a: the symbol | a top-level variable |
| `C_LSET`, `C_GSET` | a: the position or symbol, b: the expression | `set!` |
| `C_GDEF` | a: the symbol, b: the expression | a top-level definition |
| `C_IF` | a: a chain of the test, the consequent, and the alternative | `if` |
| `C_LAMBDA` | a: the number of fixed variables, b: 1 with a rest variable, c: the chain of the body | `lambda` |
| `C_APP` | a: the operator, b: the chain of the operands, or `NONE` | a call |
| `C_CHAIN` | a: a code, b: the next cell, or `NONE` | a sequence |

The environment of a call holds the fixed variables from the first, then the rest variable, then
the environment of the closure, so the position of the `i`-th fixed variable is `i` within the
body. -/

namespace Demos.Scheme.Machine

def C_CONST : UInt64 := 1
def C_LREF : UInt64 := 2
def C_GREF : UInt64 := 3
def C_LSET : UInt64 := 4
def C_GSET : UInt64 := 5
def C_GDEF : UInt64 := 6
def C_IF : UInt64 := 7
def C_LAMBDA : UInt64 := 8
def C_APP : UInt64 := 9
def C_CHAIN : UInt64 := 10

@[inline] def codeKind (sub : UInt64) : UInt64 := mkKind K_CODE sub 0

/-- A new code node; its reference becomes `val`. -/
@[inline] def node (m : Machine) (sub a b c : UInt64) : Machine := alloc m (codeKind sub) a b c 0

/-- A chain of the codes `x` and `y`. -/
def chain2 (m : Machine) (x y : UInt64) : Machine :=
  let m := node m C_CHAIN y NONE 0
  node m C_CHAIN x m.val 0

/-- A call of the standard procedure `p` on the codes `x` and `y`. -/
def callPrim2 (m : Machine) (p x y : UInt64) : Machine :=
  let m := node m C_CONST (mkPrim p) 0 0
  let f := m.val
  let m := chain2 m x y
  node m C_APP f m.val 0

/-- A call of the standard procedure `p` on the code `x`. -/
def callPrim1 (m : Machine) (p x : UInt64) : Machine :=
  let m := node m C_CONST (mkPrim p) 0 0
  let f := m.val
  let m := node m C_CHAIN x NONE 0
  node m C_APP f m.val 0

/-- `(begin sequence)` by its rule, `((lambda () sequence))`, for the chain `body`. -/
def beginCore (m : Machine) (body : UInt64) : Machine :=
  let m := node m C_LAMBDA 0 0 body
  node m C_APP m.val NONE 0

/-- `(let ((x first) (thunk (lambda () rest))) body)` by the rule of `let`, for a body whose
code is `body`: `((lambda (x thunk) body) first (lambda () rest))`. -/
def twoTempLet (m : Machine) (first rest body : UInt64) : Machine :=
  let m := node m C_CHAIN rest NONE 0
  let m := node m C_LAMBDA 0 0 m.val
  let m := chain2 m first m.val
  let args := m.val
  let m := node m C_CHAIN body NONE 0
  let m := node m C_LAMBDA 2 0 m.val
  node m C_APP m.val args 0

/-- `(or first rest …)` by its rule: `(let ((x first) (thunk (lambda () (or rest …))))
(if x x (thunk)))`, with `x` and `thunk` at positions 0 and 1. -/
def orCore (m : Machine) (first rest : UInt64) : Machine :=
  let m := node m C_LREF 1 0 0
  let m := node m C_APP m.val NONE 0
  let call := m.val
  let m := node m C_LREF 0 0 0
  let x1 := m.val
  let m := node m C_LREF 0 0 0
  let x2 := m.val
  let m := node m C_CHAIN call NONE 0
  let m := node m C_CHAIN x2 m.val 0
  let m := node m C_CHAIN x1 m.val 0
  let m := node m C_IF m.val 0 0
  twoTempLet m first rest m.val

/-- `(and first rest …)` by its rule: `(let ((x first) (thunk (lambda () (and rest …))))
(if x (thunk) x))`. -/
def andCore (m : Machine) (first rest : UInt64) : Machine :=
  let m := node m C_LREF 1 0 0
  let m := node m C_APP m.val NONE 0
  let call := m.val
  let m := node m C_LREF 0 0 0
  let x1 := m.val
  let m := node m C_LREF 0 0 0
  let x2 := m.val
  let m := node m C_CHAIN x2 NONE 0
  let m := node m C_CHAIN call m.val 0
  let m := node m C_CHAIN x1 m.val 0
  let m := node m C_IF m.val 0 0
  twoTempLet m first rest m.val

end Demos.Scheme.Machine
