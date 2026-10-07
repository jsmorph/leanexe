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

/-- The instructions of an operation after the code of its operands, with the first scratch
local `base`.  WebAssembly traps on a zero divisor, so division and remainder save their operands
in locals `base` and `base + 1`, test the divisor, and give Lean's result for zero: 0 for division
and the dividend for the remainder. -/
def BinOp.code (op : BinOp) (base : Nat) : Program :=
  match op with
  | .add => [.addI64]
  | .sub => [.subI64]
  | .mul => [.mulI64]
  | .div => [.localSet (base + 1), .localSet base, .localGet (base + 1), .eqzI64,
      .iff 0 1 [.constI64 0] [.localGet base, .localGet (base + 1), .divUI64] [] [.i64]]
  | .rem => [.localSet (base + 1), .localSet base, .localGet (base + 1), .eqzI64,
      .iff 0 1 [.localGet base] [.localGet base, .localGet (base + 1), .remUI64] [] [.i64]]
  | .and => [.andI64]
  | .or => [.orI64]
  | .xor => [.xorI64]
  | .shl => [.shlI64]
  | .shr => [.shrUI64]

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

/-- The instructions of the arguments, in order. -/
def argsCode : {ps : List Ty} → ((i : Fin ps.length) → Program) → Program
  | [], _ => []
  | _ :: _, c => c ⟨0, by simp⟩ ++ argsCode fun i => c i.succ

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

/-- The instructions that allocate a block of the byte count on top of the stack, put its address
in local `ptr`, and write the word in local `len` as its length word. -/
def allocBlockCode (len ptr : Nat) : Program :=
  [.call 0, .localSet ptr, .localGet ptr, .wrapI64, .localGet len, .store64 0]

/-- The instructions that allocate an array of as many words as local `count` holds, put its
address in local `ptr`, and write its length word. -/
def allocArrayCode (count ptr : Nat) : Program :=
  [.localGet count, .constI64 1, .addI64, .constI64 8, .mulI64] ++ allocBlockCode count ptr

/-- The loop that copies the elements of the array at the address in local `src`, as many as
local `count` holds, to the words from the address in local `dst` on, element `i` to the word at
`dst + (i + 1) * 8`.  Local `index` holds the index. -/
def copyIntoCode (src dst count index : Nat) : Program :=
  [.constI64 0, .localSet index,
    .block 0 0 [.loop 0 0 [.localGet index, .localGet count, .geUI64, .br_if 1,
      .localGet dst, .localGet index, .constI64 1, .addI64, .constI64 8, .mulI64, .addI64,
      .wrapI64,
      .localGet src, .localGet index, .constI64 1, .addI64, .constI64 8, .mulI64, .addI64,
      .wrapI64, .load64 0, .store64 0,
      .localGet index, .constI64 1, .addI64, .localSet index, .br 0]]]

/-- The instructions that copy the array whose address local `src` holds into a new array and
push the new array's address.  Local `base` holds the length, `base + 1` the new address, and
`base + 2` the index of the element being copied. -/
def copyArrayCode (src base : Nat) : Program :=
  [.localGet src, .wrapI64, .load64 0, .localSet base] ++ allocArrayCode base (base + 1) ++
    copyIntoCode src (base + 1) base (base + 2) ++ [.localGet (base + 1)]

/-- The instructions that push a copy of the value of type `t` whose words locals `src` on hold:
each array copied into a new array, and the other words as they are. -/
def copyCode : Ty → Nat → Nat → Program
  | .word, src, _ | .bool, src, _ => [.localGet src]
  | .pair a b, src, base => copyCode a src base ++ copyCode b (src + a.width) base
  | .array, src, base => copyArrayCode src base

/-- The instructions that release the arrays of the owned value of type `t` whose words locals
`src` on hold. -/
def releaseCode : Ty → Nat → Program
  | .word, _ | .bool, _ => []
  | .pair a b, src => releaseCode a src ++ releaseCode b (src + a.width)
  | .array, src => [.localGet src, .call 1]

/-- The locals that a copy of a value of type `t` uses: three for each array's copy, and none
for a value without arrays. -/
def Ty.copyScratch (t : Ty) : Nat := if t.scalar then 0 else 3

/-- The locals that turning a borrowed value of type `t` on the stack into an owned copy needs:
its words, and three for the copy of each array. -/
def copyWidth (t : Ty) : Nat := if t.scalar then 0 else t.width + 3

/-- The instructions that turn the value of type `t` on top of the stack, held in mode `source`,
into one held in mode `target`: a borrowed value that must be owned is stored in the locals from
`base` on and copied. -/
def coerceCode (t : Ty) (source target : Mode) (base : Nat) : Program :=
  if source = .borrowed ∧ target = .owned ∧ t.scalar = false then
    storeCode base t.width ++ copyCode t base (base + t.width)
  else []

/-- The instructions that release variable `i` among the variables of types `Γ` in the slots
`slots`, when it is owned. -/
def releaseVar (Γ : List Ty) (slots : List Slot) (i : Nat) : Program :=
  match Γ[i]? with
  | some t =>
    if (slots.getD i default).mode = .owned then releaseCode t (slots.getD i default).loc else []
  | none => []

/-- The instructions that release the owned variables that `sel` selects, by index, among the
variables of types `Γ` in the slots `slots`. -/
def releaseWhere (Γ : List Ty) (slots : List Slot) (sel : Nat → Bool) : Program :=
  ((List.range Γ.length).filter sel).flatMap (releaseVar Γ slots)

/-- The instructions that push the words of variable `x`: a copy when it is owned and stays live
in `live`, and its own words otherwise, which move it when it is owned. -/
def Var.code (slots : List Slot) (base : Nat) (live : Nat → Bool) {Γ : List Ty} {t : Ty}
    (x : Var Γ t) : Program :=
  if (slots.getD x.index default).mode = .owned ∧ live x.index = true then
    copyCode t (slots.getD x.index default).loc base
  else loadCode (slots.getD x.index default).loc t.width

/-- The instructions that push the words of variable `x` as an owned value: its own words when it
is owned and dies, and a copy otherwise. -/
def Var.ownedCode (slots : List Slot) (base : Nat) (live : Nat → Bool) {Γ : List Ty} {t : Ty}
    (x : Var Γ t) : Program :=
  x.code slots base live ++ coerceCode t (slots.getD x.index default).mode .owned base

/-- The mode that holds both of two values' arrays: owned when either is owned. -/
def Mode.join : Mode → Mode → Mode
  | .borrowed, .borrowed => .borrowed
  | _, _ => .owned

/-- The mode of an expression's value, given the modes of the variables: owned when it holds
arrays that its holder must consume, which a call's result, a built or updated array, a moved or
copied variable, and a join of an owned value do. -/
def Expr.mode (modes : List Mode) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Mode
  | _, _, .var x => modes.getD x.index .borrowed
  | _, _, .ite _ thenE elseE => (thenE.mode modes).join (elseE.mode modes)
  | _, _, .letE value body => body.mode (value.mode modes :: modes)
  | _, _, .call (g := g) _ _ => if g.result.scalar then .borrowed else .owned
  | _, _, .build _ _ | _, _, .set _ _ _ => .owned
  | _, _, .pair first second => (first.mode modes).join (second.mode modes)
  | _, _, .letPair e body => body.mode (e.mode modes :: e.mode modes :: modes)
  | _, _, .loop _ init body =>
    (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
  | _, _, _ => .borrowed

/-- The instructions that push the words of a variable or a pair of such expressions, read in
place. -/
def Expr.placeCode (slots : List Slot) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Program
  | _, _, .var (t := t) x => loadCode (slots.getD x.index default).loc t.width
  | _, _, .pair first second => first.placeCode slots ++ second.placeCode slots
  | _, _, _ => []

/-- The locals that an expression needs from its first free local on: the words of each `letE`
and `letPair` value and of each `ite` result, two for each division or remainder, the count, the
index, and the state of each loop, the position of each read, the count, the address, and the
index of each `build`, the position, the value, and the address of each `set`, and the locals of
each copy, on a path of the expression.  A call's
arguments and a pair's components leave their words on the stack, so they share their locals. -/
def Expr.width : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat
  | _, _, .word _ | _, _, .bool _ | _, _, .size _ => 0
  | _, _, .var (t := t) _ => t.copyScratch
  | _, _, .bin op left right => max op.scratch (max left.width right.width)
  | _, _, .cmp _ left right | _, _, .and left right | _, _, .or left right =>
    max left.width right.width
  | _, _, .not e => e.width
  | _, _, .ite (t := t) c thenE elseE =>
    max c.width (t.width + max (max thenE.width elseE.width) (copyWidth t))
  | _, _, .letE (s := s) value body => s.width + max value.width body.width
  | _, _, .call _ args => argsMax fun i => (args i).width
  | _, _, .pair (s := s) (t := t) first second =>
    max (max first.width second.width) (max (copyWidth s) (copyWidth t))
  | _, _, .letPair (s := s) (t := t) e body => s.width + t.width + max e.width body.width
  | _, _, .loop (t := t) count init body =>
    max count.width (max (1 + max init.width (copyWidth t))
      (2 + t.width + max body.width (copyWidth t)))
  | _, _, .get _ i => max i.width 1
  | _, _, .build count elem => max count.width (3 + elem.width)
  | _, _, .set _ i v => max i.width (max (1 + v.width) (2 + copyWidth .array))

/-- The instructions that push the words that hold the value of an expression.  Variable `x`
starts at local `(slots.getD x.index default).loc`, the locals from `base` on are free, and
`live` gives the variables live after the expression, which each subexpression receives together
with those that the rest of the expression reads.  Each expression consumes the owned variables
that die in it: a variable moves where it dies and is copied where it stays live, a reader
releases a dying variable it reads, and a branch, a binding, and a loop release the owned
variables that die without a use.  A comparison widens its 32-bit result to a word.  `ite` tests
its condition with `i64.eqz`, so its `if` runs the else branch first, and each branch stores its
words in the locals from `base` on, which the code loads after the `if`: the encoder writes block
types of at most one result.  `letE` stores its value from local `base` on and gives its body the
locals above it, and `letPair` stores its first component from `base` on and its second after
it.  A call pushes its arguments in order, its arrays read in place, and calls the function.  A
loop keeps its count in local `base`, its index in local `base + 1`, and its state from local
`base + 2` on, and leaves the block when the index reaches the count.  `size` loads the length
word at the array's address.  `get` keeps the position in local `base`, compares it with the
length word, and loads the element or yields 0.  `build` keeps its count in local `base`, traps
at `unreachable` when the count is `2 ^ 29` or more, since the array would not fit in 32-bit
memory, allocates the array into local `base + 1`, and keeps the index in local `base + 2`.  For
each index it pushes the element's address, runs the element's code, and stores the element; the
outer variables that only the element reads stay live through the loop and are released after
it.  `set` keeps the position in local `base` and the value in local `base + 1`, then takes the
array as owned, in local `base + 2`, and writes the element when the position is below the
length: an owned array that dies there is updated in its own block, and any other is copied
first. -/
def Expr.code (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Program
  | _, _, .word value => [.constI64 value]
  | _, _, .bool value => [.constI64 (boolWord value)]
  | _, _, .var x => x.code slots base live
  | _, _, .bin op left right =>
    left.code slots base (fun i => live i || right.uses i) ++ right.code slots base live ++
      op.code base
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
  | Γ, _, .ite (t := t) c thenE elseE =>
    let modes := slots.map Slot.mode
    let mode := (thenE.mode modes).join (elseE.mode modes)
    let mid := fun i => live i || thenE.uses i || elseE.uses i
    c.code slots base mid ++
      [.eqzI64, .iff 0 0
        (releaseWhere Γ slots (fun i => mid i && !(live i || elseE.uses i)) ++
          elseE.code slots (base + t.width) live ++
          coerceCode t (elseE.mode modes) mode (base + t.width) ++ storeCode base t.width)
        (releaseWhere Γ slots (fun i => mid i && !(live i || thenE.uses i)) ++
          thenE.code slots (base + t.width) live ++
          coerceCode t (thenE.mode modes) mode (base + t.width) ++ storeCode base t.width)
        [] []] ++
      loadCode base t.width
  | _, _, .letE (s := s) value body =>
    let mode := value.mode (slots.map Slot.mode)
    value.code slots (base + s.width) (fun i => live i || body.uses (i + 1)) ++
      storeCode base s.width ++
      (if mode = .owned ∧ body.uses 0 = false then releaseCode s base else []) ++
      body.code (⟨base, mode⟩ :: slots) (base + s.width) (shift 1 live)
  | Γ, _, .call (g := g) f args =>
    let all := fun i => live i || argsAny fun j => (args j).uses i
    argsCode (fun i =>
      if (g.params.get i).scalar then (args i).code slots base all
      else (args i).placeCode slots) ++
      [.call f.callIndex] ++
      releaseWhere Γ slots (fun i => (argsAny fun j => (args j).uses i) && !live i)
  | _, _, .pair (s := s) (t := t) first second =>
    let modes := slots.map Slot.mode
    let mode := (first.mode modes).join (second.mode modes)
    first.code slots base (fun i => live i || second.uses i) ++
      coerceCode s (first.mode modes) mode base ++
      second.code slots base live ++ coerceCode t (second.mode modes) mode base
  | _, _, .letPair (s := s) (t := t) e body =>
    let mode := e.mode (slots.map Slot.mode)
    e.code slots (base + s.width + t.width) (fun i => live i || body.uses (i + 2)) ++
      storeCode (base + s.width) t.width ++ storeCode base s.width ++
      (if mode = .owned ∧ body.uses 1 = false then releaseCode s base else []) ++
      (if mode = .owned ∧ body.uses 0 = false then releaseCode t (base + s.width) else []) ++
      body.code (⟨base + s.width, mode⟩ :: ⟨base, mode⟩ :: slots) (base + s.width + t.width)
        (shift 2 live)
  | Γ, _, .loop (t := t) count init body =>
    let modes := slots.map Slot.mode
    let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
    count.code slots base (fun i => live i || init.uses i || body.uses (i + 2)) ++
      [.localSet base] ++ init.code slots (base + 1) (fun i => live i || body.uses (i + 2)) ++
      coerceCode t (init.mode modes) mode (base + 1) ++
      storeCode (base + 2) t.width ++ [.constI64 0, .localSet (base + 1),
        .block 0 0 [.loop 0 0 ([.localGet (base + 1), .localGet base, .geUI64, .br_if 1] ++
          (if mode = .owned ∧ body.uses 0 = false then releaseCode t (base + 2) else []) ++
          body.code (⟨base + 2, mode⟩ :: ⟨base + 1, .borrowed⟩ :: slots)
            (base + 2 + t.width) (shift 2 fun i => live i || body.uses (i + 2)) ++
          coerceCode t (body.mode (mode :: .borrowed :: modes)) mode (base + 2 + t.width) ++
          storeCode (base + 2) t.width ++
          [.localGet (base + 1), .constI64 1, .addI64, .localSet (base + 1), .br 0]) [] []]
          [] []] ++
      releaseWhere Γ slots (fun i => body.uses (i + 2) && !live i) ++
      loadCode (base + 2) t.width
  | _, _, .size x =>
    [.localGet (slots.getD x.index default).loc, .wrapI64, .load64 0] ++
      (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode .array (slots.getD x.index default).loc else [])
  | _, _, .get x i =>
    i.code slots base (fun k => live k || k == x.index) ++
      [.localSet base, .localGet base, .localGet (slots.getD x.index default).loc, .wrapI64,
        .load64 0, .ltUI64,
        .iff 0 1 [.localGet (slots.getD x.index default).loc, .localGet base, .constI64 1,
          .addI64, .constI64 8, .mulI64, .addI64, .wrapI64, .load64 0] [.constI64 0] [] [.i64]] ++
      (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode .array (slots.getD x.index default).loc else [])
  | _, _, .set x i v =>
    i.code slots base (fun k => live k || k == x.index || v.uses k) ++ [.localSet base] ++
      v.code slots (base + 1) (fun k => live k || k == x.index) ++ [.localSet (base + 1)] ++
      x.ownedCode slots (base + 2) live ++
      [.localSet (base + 2), .localGet base, .localGet (base + 2), .wrapI64, .load64 0, .ltUI64,
        .iff 0 0 [.localGet (base + 2), .localGet base, .constI64 1, .addI64, .constI64 8,
          .mulI64, .addI64, .wrapI64, .localGet (base + 1), .store64 0] [] [] [],
        .localGet (base + 2)]
  | Γ, _, .build count elem =>
    let all := fun i => live i || elem.uses (i + 1)
    count.code slots base all ++
      [.localSet base, .localGet base, .constI64 536870912, .geUI64,
        .iff 0 0 [.unreachable] [] [] []] ++
      allocArrayCode base (base + 1) ++
      [.constI64 0, .localSet (base + 2),
        .block 0 0 [.loop 0 0 ([.localGet (base + 2), .localGet base, .geUI64, .br_if 1,
          .localGet (base + 1), .localGet (base + 2), .constI64 1, .addI64, .constI64 8, .mulI64,
          .addI64, .wrapI64] ++
          elem.code (⟨base + 2, .borrowed⟩ :: slots) (base + 3) (shift 1 all) ++
          [.store64 0, .localGet (base + 2), .constI64 1, .addI64, .localSet (base + 2), .br 0])
          [] []] [] []] ++
      releaseWhere Γ slots (fun i => elem.uses (i + 1) && !live i) ++ [.localGet (base + 1)]

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
    locals := List.replicate (func.body.width + copyWidth func.result) .i64
    body := func.body.code (paramSlots func.params 0) (widthSum func.params) (fun _ => false) ++
      coerceCode func.result (func.body.mode ((paramSlots func.params 0).map Slot.mode)) .owned
        (widthSum func.params + func.body.width)
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
