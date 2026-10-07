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

/-- The largest of the numbers `w i`, or 0. -/
def argsMax : {ps : List Ty} → ((i : Fin ps.length) → Nat) → Nat
  | [], _ => 0
  | _ :: _, w => max (w ⟨0, by simp⟩) (argsMax fun i => w i.succ)

/-- The instructions of the arguments, in order: argument `i`'s code `c i live` for the variables
`live` live after it, which are those live after the call and those that later arguments read,
given by `uses`. -/
def argsCode : {ps : List Ty} → ((i : Fin ps.length) → (Nat → Bool) → Program) →
    ((i : Fin ps.length) → Nat → Bool) → (Nat → Bool) → Program
  | [], _, _, _ => []
  | _ :: _, c, uses, live =>
    c ⟨0, by simp⟩ (fun k => live k || argsAny fun i => uses i.succ k) ++
      argsCode (fun i => c i.succ) (fun i => uses i.succ) live

/-- The module index of a function that an expression calls: the functions `S` occupy the module
positions from 2, the last of `S` first. -/
def FVar.callIndex {S : List Sig} {g : Sig} (f : FVar S g) : Nat :=
  2 + (S.length - 1 - f.index)

/-- The instructions that push the words in locals `loc` to `loc + w - 1`, in order. -/
def loadCode (loc : Nat) : Nat → Program
  | 0 => []
  | w + 1 => .localGet loc :: loadCode (loc + 1) w

/-- The instructions that store the top `w` words of the stack in locals `loc` to `loc + w - 1`,
the top word in the last of them. -/
def storeCode (loc : Nat) : Nat → Program
  | 0 => []
  | w + 1 => storeCode (loc + 1) w ++ [.localSet loc]

/-- How a variable holds an array: borrowed, readable while the variable is in scope, or owned,
which its holder must consume. -/
inductive Mode where
  | borrowed | owned
  deriving DecidableEq, Repr, Inhabited

/-- Where a variable's words start, and its mode. -/
structure Slot where
  loc : Nat
  mode : Mode
  deriving Inhabited

/-- The variables live in a body that binds `k` new variables, given those live after the
binder: the new variables are dead after the body. -/
def shift (k : Nat) (live : Nat → Bool) (i : Nat) : Bool := if i < k then false else live (i - k)

/-- The number of words that hold the values of the types. -/
def widthSum (ts : List Ty) : Nat := (ts.map Ty.width).sum

/-- The locals that an expression needs from its first free local on: the words of each `letE`
and `letPair` value and of each `ite` result, two for each division or remainder, and the count,
the index, and the state of each loop, on a path of the expression.  A call's arguments and a
pair's components leave their words on the stack, so they share their locals. -/
def Expr.width : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat
  | _, _, .word _ | _, _, .bool _ | _, _, .var _ => 0
  | _, _, .bin op left right => op.scratch + max left.width right.width
  | _, _, .cmp _ left right | _, _, .and left right | _, _, .or left right =>
    max left.width right.width
  | _, _, .not e => e.width
  | _, _, .ite (t := t) c thenE elseE => max c.width (t.width + max thenE.width elseE.width)
  | _, _, .letE (s := s) value body => s.width + max value.width body.width
  | _, _, .call _ args => argsMax fun i => (args i).width
  | _, _, .pair first second => max first.width second.width
  | _, _, .letPair (s := s) (t := t) e body => s.width + t.width + max e.width body.width
  | _, _, .loop (t := t) count init body =>
    max count.width (max (1 + init.width) (2 + t.width + body.width))
  | _, _, .size a => a.width
  | _, _, .get a i => max a.width (max 2 (1 + i.width))

/-- The instructions that push the words that hold the value of an expression.  Variable `x`
starts at local `(slots.getD x.index default).loc`, the locals from `base` on are free, and
`live` gives the variables live after the expression, which each subexpression receives together
with those that the rest of the expression reads.  A comparison widens its 32-bit result to a
word.  `ite` tests its condition with `i64.eqz`, so its `if` runs the else branch first, and each
branch stores its words in the locals from `base` on, which the code loads after the `if`: the
encoder writes block types of at most one result.  `letE` stores its value from local `base` on
and gives its body the locals above it, and `letPair` stores its first component from `base` on
and its second after it.  A call pushes its arguments in order and calls the function.  A loop
keeps its count in local `base`, its index in local `base + 1`, and its state from local
`base + 2` on, and leaves the block when the index reaches the count.  `size` loads the length
word at the array's address.  `get` keeps the array's address in local `base` and the position in
local `base + 1`, compares the position with the length word, and loads the element or yields
0. -/
def Expr.code (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Program
  | _, _, .word value => [.constI64 value]
  | _, _, .bool value => [.constI64 (boolWord value)]
  | _, _, .var (t := t) x => loadCode (slots.getD x.index default).loc t.width
  | _, _, .bin op left right =>
    op.code base (left.code slots (base + op.scratch) fun i => live i || right.uses i)
      (right.code slots (base + op.scratch) live)
  | _, _, .cmp op left right =>
    left.code slots base (fun i => live i || right.uses i) ++ right.code slots base live ++
      [op.instr, .extendUI32]
  | _, _, .not e => e.code slots base live ++ [.eqzI64, .extendUI32]
  | _, _, .and left right =>
    left.code slots base (fun i => live i || right.uses i) ++ right.code slots base live ++
      [.andI64]
  | _, _, .or left right =>
    left.code slots base (fun i => live i || right.uses i) ++ right.code slots base live ++
      [.orI64]
  | _, _, .ite (t := t) c thenE elseE =>
    c.code slots base (fun i => live i || thenE.uses i || elseE.uses i) ++
      [.eqzI64, .iff 0 0 (elseE.code slots (base + t.width) live ++ storeCode base t.width)
        (thenE.code slots (base + t.width) live ++ storeCode base t.width) [] []] ++
      loadCode base t.width
  | _, _, .letE (s := s) value body =>
    value.code slots (base + s.width) (fun i => live i || body.uses (i + 1)) ++
      storeCode base s.width ++
      body.code (⟨base, .borrowed⟩ :: slots) (base + s.width) (shift 1 live)
  | _, _, .call f args =>
    argsCode (fun i live => (args i).code slots base live) (fun i => (args i).uses) live ++
      [.call f.callIndex]
  | _, _, .pair first second =>
    first.code slots base (fun i => live i || second.uses i) ++ second.code slots base live
  | _, _, .letPair (s := s) (t := t) e body =>
    e.code slots (base + s.width + t.width) (fun i => live i || body.uses (i + 2)) ++
      storeCode (base + s.width) t.width ++ storeCode base s.width ++
      body.code (⟨base + s.width, .borrowed⟩ :: ⟨base, .borrowed⟩ :: slots)
        (base + s.width + t.width) (shift 2 live)
  | _, _, .loop (t := t) count init body =>
    count.code slots base (fun i => live i || init.uses i || body.uses (i + 2)) ++
      [.localSet base] ++ init.code slots (base + 1) (fun i => live i || body.uses (i + 2)) ++
      storeCode (base + 2) t.width ++ [.constI64 0, .localSet (base + 1),
        .block 0 0 [.loop 0 0 ([.localGet (base + 1), .localGet base, .geUI64, .br_if 1] ++
          body.code (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: slots)
            (base + 2 + t.width) (shift 2 fun i => live i || body.uses (i + 2)) ++
          storeCode (base + 2) t.width ++
          [.localGet (base + 1), .constI64 1, .addI64, .localSet (base + 1), .br 0]) [] []]
          [] []] ++
      loadCode (base + 2) t.width
  | _, _, .size a => a.code slots base live ++ [.wrapI64, .load64 0]
  | _, _, .get a i =>
    a.code slots base (fun k => live k || i.uses k) ++ [.localSet base] ++
      i.code slots (base + 1) live ++
      [.localSet (base + 1), .localGet (base + 1), .localGet base, .wrapI64, .load64 0, .ltUI64,
        .iff 0 1 [.localGet base, .localGet (base + 1), .constI64 1, .addI64, .constI64 8, .mulI64,
          .addI64, .wrapI64, .load64 0] [.constI64 0] [] [.i64]]

/-- The slots of a function's parameters, all borrowed: parameter `i` starts after the words of
the parameters before it. -/
def paramSlots : List Ty → Nat → List Slot
  | [], _ => []
  | t :: ts, loc => ⟨loc, .borrowed⟩ :: paramSlots ts (loc + t.width)

def Func.type (func : Func S) : FuncType :=
  { params := List.replicate (widthSum func.params) .i64
    results := List.replicate func.result.width .i64 }

/-- The function's code: the words of the arguments are its first locals, the locals that the
body needs follow them, and the body leaves the words of the result on the stack. -/
def Func.function (func : Func S) (typeIdx : Nat) : Wasm.Function :=
  { params := func.type.params
    locals := List.replicate func.body.width .i64
    body := func.body.code (paramSlots func.params 0) (widthSum func.params) fun _ => false
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

/-- A program's functions in module order, the last of the list first, from position 2. -/
def Prog.functions : {S : List Sig} → Prog S → List Wasm.Function
  | _, .nil => []
  | _, .cons (S := S) f rest => rest.functions ++ [f.function (2 + S.length)]

def Prog.types : {S : List Sig} → Prog S → List FuncType
  | _, .nil => []
  | _, .cons f rest => rest.types ++ [f.type]

def Prog.exports : {S : List Sig} → Prog S → List Export
  | _, .nil => []
  | _, .cons (S := S) f rest => rest.exports ++ [{ name := f.name, funcIdx := 2 + S.length }]

/-- The module of a program, each function exported under its name.  Functions 0 and 1 are the
runtime's `alloc` and `release`, and the program's functions follow them, each with the type of
its own index. -/
def compile (prog : Prog S) : Module :=
  let types := [wordToWord, wordToNone] ++ prog.types
  { funcs := [LeanExe.Runtime.allocFunction 0, LeanExe.Runtime.releaseFunction 1] ++
      prog.functions
    exports := [{ name := "alloc", funcIdx := 0 }, { name := "release", funcIdx := 1 }] ++
      prog.exports
    memory := some { pagesMin := 16, pagesMax := some 65535 }
    globals := runtimeGlobals
    types
    gcTypes := types.map fun type => { comp := .func type }
    globalExports := [("allocCount", 2), ("freeCount", 3)]
    memoryExports := [("memory", 0)] }

theorem Prog.functions_length (prog : Prog S) : prog.functions.length = S.length := by
  induction prog with
  | nil => rfl
  | cons f rest ih => simp [Prog.functions, ih]

theorem compile_funcs (prog : Prog S) (k : Nat) :
    (compile prog).funcs[2 + k]? = prog.functions[k]? := by
  conv_lhs => rw [show 2 + k = k + 1 + 1 by omega]
  simp [compile]

end Verified
