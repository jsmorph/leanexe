/-!
The PTX subset of the kernels.  A kernel has one entry point whose parameters are 64-bit pointers
to global buffers: the read-only inputs, then the output.  Registers fall into three classes,
`.b32`, `.b64`, and `.pred`.  The instructions are integer arithmetic, comparisons, selection,
conversions, the special registers that identify a thread, loads of parameters, and loads and
stores of aligned 64-bit words.  Any instruction may carry a guard.  Control flow is structured: a
conditional, a loop whose condition is computed by a statement list, and `ret`.  The printer writes
the conditional and the loop as labels and guarded branches.  Registers and parameters are
numbered; the printer names them `%w`, `%d`, `%p`, and `b`, each followed by eight hexadecimal
digits.
-/

namespace LeanExe.PTX

/-- An operand of an instruction on 64-bit words: a `.b64` register or an immediate. -/
inductive Src64 where
  | reg (index : Nat)
  | imm (value : UInt64)
  deriving Repr, DecidableEq

/-- An operand of an instruction on 32-bit words: a `.b32` register or an immediate. -/
inductive Src32 where
  | reg (index : Nat)
  | imm (value : UInt32)
  deriving Repr, DecidableEq

/-- The special registers `%tid.x`, `%ntid.x`, and `%ctaid.x`. -/
inductive Special where
  | tidX
  | ntidX
  | ctaidX
  deriving Repr, DecidableEq

/-- Binary operations on 64-bit words: `add.u64`, `sub.u64`, `mul.lo.u64`, `div.u64`,
`rem.u64`, `and.b64`, `or.b64`, and `xor.b64`. -/
inductive Bin64 where
  | add
  | sub
  | mulLo
  | div
  | rem
  | and
  | or
  | xor
  deriving Repr, DecidableEq

/-- `shl.b64` and `shr.b64`. -/
inductive Shift where
  | shl
  | shr
  deriving Repr, DecidableEq

/-- Comparisons of `setp` on `.u64` operands. -/
inductive Cmp where
  | eq
  | ne
  | lt
  | le
  deriving Repr, DecidableEq

inductive Instr where
  /-- `mov.u32 d, %tid.x` and the other special registers. -/
  | special (d : Nat) (s : Special)
  /-- `mov.b32 d, a` -/
  | mov32 (d : Nat) (a : Src32)
  /-- `mov.b64 d, a` -/
  | mov64 (d : Nat) (a : Src64)
  /-- A binary operation on 64-bit words, `op d, a, b`. -/
  | bin64 (op : Bin64) (d a : Nat) (b : Src64)
  /-- `shl.b64 d, a, b` or `shr.b64 d, a, b`, with a `.u32` amount `b`. -/
  | shift (op : Shift) (d a : Nat) (b : Src32)
  /-- `setp.c.u64 p, a, b` -/
  | setp (c : Cmp) (p a : Nat) (b : Src64)
  /-- `selp.b64 d, t, f, p`: `t` when `p` holds, and otherwise `f`. -/
  | selp (d : Nat) (t f : Src64) (p : Nat)
  /-- `not.pred d, a` -/
  | notPred (d a : Nat)
  /-- `cvt.u64.u32 d, a` -/
  | widen (d a : Nat)
  /-- `cvt.u32.u64 d, a` -/
  | narrow (d a : Nat)
  /-- `mad.wide.u32 d, a, b, c`: the 64-bit product of the `.b32` registers `a` and `b`, plus the
  `.b64` register `c`. -/
  | madWide (d a b c : Nat)
  /-- `ld.param.u64 d, [b]`, for parameter `b`. -/
  | ldParam (d param : Nat)
  /-- `cvta.to.global.u64 d, a` -/
  | cvtaGlobal (d a : Nat)
  /-- `ld.global.u64 d, [a + offset]` -/
  | ld (d a : Nat) (offset : UInt64)
  /-- `st.global.u64 [a + offset], v` -/
  | st (a : Nat) (offset : UInt64) (v : Nat)
  deriving Repr, DecidableEq

/-- A guard `@p` (`negated = false`) or `@!p` (`negated = true`). -/
structure Guard where
  negated : Bool
  pred : Nat
  deriving Repr, DecidableEq

inductive Stmt where
  /-- An instruction, with an optional guard. -/
  | instr (guard : Option Guard) (i : Instr)
  /-- Run `thenStmts` when predicate `p` holds, and otherwise `elseStmts`. -/
  | ite (p : Nat) (thenStmts elseStmts : List Stmt)
  /-- Run `cond`, then end the loop unless predicate `p` holds, then run `body`, and repeat. -/
  | while_ (cond : List Stmt) (p : Nat) (body : List Stmt)
  | ret
  deriving Repr

/-- A kernel: input buffers at parameters `0` to `inputs - 1`, the output at parameter `inputs`,
`regs32` registers of class `.b32`, `regs64` of class `.b64`, and `preds` of class `.pred`. -/
structure Module where
  inputs : Nat
  regs32 : Nat
  regs64 : Nat
  preds : Nat
  body : List Stmt
  deriving Repr

end LeanExe.PTX
