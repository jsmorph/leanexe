import Verified.Source
import LeanExe.Runtime.Defs

/-! The verified compiler: a Lean function from source functions to a WebAssembly module.  The
module has the layout of `LeanExe`'s modules, with the runtime's `alloc` and `release` at
functions 0 and 1, so the runtime and its proofs serve both compilers. -/

namespace Verified

open Wasm

/-- The scratch locals that an operation needs for itself: two for division and remainder, which
save their operands to test the divisor. -/
def BinOp.scratch : BinOp → Nat
  | .div | .rem => 2
  | _ => 0

/-- The instructions of an operation, given the code of its operands and the first scratch local
`base`.  WebAssembly traps on a zero divisor, so division and remainder save their operands in
locals `base` and `base + 1`, test the divisor, and give Lean's result for zero: 0 for division
and the dividend for the remainder. -/
def BinOp.code (op : BinOp) (base : Nat) (left right : Program) : Program :=
  match op with
  | .add => left ++ right ++ [.addI64]
  | .sub => left ++ right ++ [.subI64]
  | .mul => left ++ right ++ [.mulI64]
  | .div => left ++ [.localSet base] ++ right ++
      [.localSet (base + 1), .localGet (base + 1), .eqzI64,
        .iff 0 1 [.constI64 0] [.localGet base, .localGet (base + 1), .divUI64] [] [.i64]]
  | .rem => left ++ [.localSet base] ++ right ++
      [.localSet (base + 1), .localGet (base + 1), .eqzI64,
        .iff 0 1 [.localGet base] [.localGet base, .localGet (base + 1), .remUI64] [] [.i64]]
  | .and => left ++ right ++ [.andI64]
  | .or => left ++ right ++ [.orI64]
  | .xor => left ++ right ++ [.xorI64]
  | .shl => left ++ right ++ [.shlI64]
  | .shr => left ++ right ++ [.shrUI64]

/-- The WebAssembly comparison of a comparison. -/
def CmpOp.instr : CmpOp → Instruction
  | .eq => .eqI64
  | .ne => .neI64
  | .lt => .ltUI64
  | .le => .leUI64

/-- The locals that an expression needs from its first free local on: one for each `letE` and
two for each division or remainder on a path of the expression. -/
def Expr.width : {Γ : List Ty} → {t : Ty} → Expr Γ t → Nat
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ => 0
  | _, _, .bin op left right => op.scratch + max left.width right.width
  | _, _, .cmp _ left right | _, _, .and left right | _, _, .or left right =>
    max left.width right.width
  | _, _, .not e => e.width
  | _, _, .ite c thenE elseE => max c.width (max thenE.width elseE.width)
  | _, _, .letE value body => 1 + max value.width body.width

/-- The instructions that push the word that holds the value of an expression.  Variable `x` is
in local `locs.getD x.index 0`, and the locals from `base` on are free.  A comparison widens its
32-bit result to a word, and `ite` tests its condition with `i64.eqz`, so its `if` runs the else
branch first.  `letE` stores its value in local `base` and gives its body the locals above it. -/
def Expr.code (locs : List Nat) (base : Nat) : {Γ : List Ty} → {t : Ty} → Expr Γ t → Program
  | _, _, .word value => [.constI64 value]
  | _, _, .bool value => [.constI64 (Ty.encode .bool value)]
  | _, _, .var x => [.localGet (locs.getD x.index 0)]
  | _, _, .bin op left right =>
    op.code base (left.code locs (base + op.scratch)) (right.code locs (base + op.scratch))
  | _, _, .cmp op left right =>
    left.code locs base ++ right.code locs base ++ [op.instr, .extendUI32]
  | _, _, .not e => e.code locs base ++ [.eqzI64, .extendUI32]
  | _, _, .and left right => left.code locs base ++ right.code locs base ++ [.andI64]
  | _, _, .or left right => left.code locs base ++ right.code locs base ++ [.orI64]
  | _, _, .ite c thenE elseE =>
    c.code locs base ++
      [.eqzI64, .iff 0 1 (elseE.code locs base) (thenE.code locs base) [] [.i64]]
  | _, _, .letE value body =>
    value.code locs (base + 1) ++ [.localSet base] ++ body.code (base :: locs) (base + 1)

def Func.type (func : Func) : FuncType :=
  { params := List.replicate func.params.length .i64, results := [.i64] }

/-- The function's code: the arguments are locals 0 to `arity - 1`, the locals that the body
needs follow them, and the body leaves the result on the stack. -/
def Func.function (func : Func) (typeIdx : Nat) : Wasm.Function :=
  { params := func.type.params
    locals := List.replicate func.body.width .i64
    body := func.body.code (List.range func.params.length) func.params.length
    results := func.type.results
    typeIdx := some typeIdx }

/-- Globals 0 through 3 hold the allocator state: the bump pointer, which starts at the heap base
4096, the free-list head, and the allocation and free counters.  Copied from `LeanExe.IR`. -/
def runtimeGlobals : List GlobalDecl :=
  (4096 :: List.replicate 3 0).map fun value =>
    { init := .i64 value, declaredType := some .i64, isMut := true,
      sourceInit := some [.constI64 value] }

/-- Parameter and result types of the runtime functions.  Copied from `LeanExe.IR`. -/
def wordToWord : FuncType := { params := [.i64], results := [.i64] }
def wordToNone : FuncType := { params := [.i64], results := [] }

/-- The module for the functions `funcs`, each exported under its name.  Functions 0 and 1 are
the runtime's `alloc` and `release`, and function `2 + i` is `funcs[i]`, with type `2 + i`. -/
def compile (funcs : List (Func × String)) : Module :=
  let types := [wordToWord, wordToNone] ++ funcs.map (·.1.type)
  { funcs := [LeanExe.Runtime.allocFunction 0, LeanExe.Runtime.releaseFunction 1] ++
      funcs.mapIdx fun i entry => entry.1.function (2 + i)
    exports := [{ name := "alloc", funcIdx := 0 }, { name := "release", funcIdx := 1 }] ++
      funcs.mapIdx fun i entry => { name := entry.2, funcIdx := 2 + i }
    memory := some { pagesMin := 16, pagesMax := some 65535 }
    globals := runtimeGlobals
    types
    gcTypes := types.map fun type => { comp := .func type }
    globalExports := [("allocCount", 2), ("freeCount", 3)]
    memoryExports := [("memory", 0)] }

theorem compile_funcs {funcs : List (Func × String)} {i : Nat} {func : Func} {name : String}
    (h : funcs[i]? = some (func, name)) :
    (compile funcs).funcs[2 + i]? = some (func.function (2 + i)) := by
  conv_lhs => rw [show 2 + i = i + 1 + 1 by omega]
  simp [compile, List.getElem?_mapIdx, h]

end Verified
