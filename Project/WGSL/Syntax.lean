/-!
The WGSL subset that kernels use: storage buffers of `u32` words, one compute entry point that
receives `global_invocation_id`, `let` and `var` declarations, assignments, stores to a buffer,
conditionals, and `return`, over the types `u32`, `f32`, `bool`, and `vec2<u32>`.  Variables and
buffers are numbered; the printer names them `v` and `b` followed by eight hexadecimal digits.
-/

namespace Project.WGSL

inductive Ty where
  | u32
  | f32
  | bool
  | vec2u
  deriving Repr, DecidableEq

/-- The binary operators, each printed as one WGSL token.  WGSL overloads them by operand type,
so `add` is `u32` or `f32` addition according to its operands. -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | lt
  | le
  | eq
  | and
  | or
  deriving Repr, DecidableEq

inductive Expr where
  /-- A `u32` literal, printed as `0x` and eight hexadecimal digits followed by `u`. -/
  | lit (value : UInt32)
  | bool (value : Bool)
  | var (index : Nat)
  /-- `gid.x`, the invocation's index along x. -/
  | gidX
  /-- `.x` and `.y` of a `vec2<u32>` variable. -/
  | fst (index : Nat)
  | snd (index : Nat)
  | vec2 (low high : Expr)
  | bin (op : BinOp) (left right : Expr)
  | not (operand : Expr)
  /-- `bitcast<f32>` of a `u32`. -/
  | toF32 (operand : Expr)
  /-- `bitcast<u32>` of an `f32`. -/
  | toU32 (operand : Expr)
  | sqrt (operand : Expr)
  | abs (operand : Expr)
  /-- `select(f, t, c)`: `t` when `c` holds, and otherwise `f`. -/
  | select (falseValue trueValue condition : Expr)
  | min (left right : Expr)
  /-- `arrayLength(&b)`, the number of words in buffer `b`. -/
  | length (buffer : Nat)
  /-- `b[i]`, word `i` of buffer `b`. -/
  | index (buffer : Nat) (position : Expr)
  deriving Repr, DecidableEq

inductive Stmt where
  | let_ (index : Nat) (type : Ty) (value : Expr)
  | var (index : Nat) (type : Ty) (value : Expr)
  | assign (index : Nat) (value : Expr)
  /-- `b[i] = e;` -/
  | store (buffer : Nat) (position value : Expr)
  | ite (condition : Expr) (thenStmts elseStmts : List Stmt)
  | ret
  deriving Repr

/-- A kernel: read-only storage buffers at bindings `0` to `inputs - 1` of group 0, one
read-write storage buffer at binding `inputs`, and the entry point `main` with workgroup size
`workgroupSize` along x. -/
structure Module where
  inputs : Nat
  workgroupSize : Nat
  body : List Stmt
  deriving Repr

end Project.WGSL
