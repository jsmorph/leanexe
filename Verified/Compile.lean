import Verified.Source
import LeanExe.Runtime.Defs

/-! The verified compiler: a Lean function from source functions to a WebAssembly module.  The
module has the layout of `LeanExe`'s modules, with the runtime's `alloc` and `release` at
functions 0 and 1, so the runtime and its proofs serve both compilers. -/

namespace Verified

open Wasm

/-- The WebAssembly types of the words that hold an element, in order. -/
def Elem.types : Elem → List ValueType
  | .word | .bool => [.i64]
  | .float => [.f64]
  | .prod a b => a.types ++ b.types

@[simp] theorem Elem.types_word : Elem.types .word = [.i64] := rfl
@[simp] theorem Elem.types_bool : Elem.types .bool = [.i64] := rfl
@[simp] theorem Elem.types_float : Elem.types .float = [.f64] := rfl

/-- The WebAssembly types of the words that hold a value of type `t`, in order. -/
def Ty.types : Ty → List ValueType
  | .elem e => e.types
  | .array _ => [.i64]
  | .pair a b => a.types ++ b.types

/-- The instructions that turn a word of type `ty` on top of the stack into the i64 that holds it
in an array: a float's bit pattern moves from an f64 to an i64. -/
def toWordCode : ValueType → Program
  | .f64 => [.i64ReinterpretF64]
  | _ => []

/-- The instructions that turn the i64 that holds a word of type `ty` in an array into the
word. -/
def ofWordCode : ValueType → Program
  | .f64 => [.f64ReinterpretI64]
  | _ => []

/-- The word count `k` of an element as the code uses it, at most `2 ^ 29`.  An element of
`2 ^ 29` words or more is in no array that memory holds, so the code may use any positive count
for it, and `2 ^ 29` keeps the count positive and below `2 ^ 64`. -/
def wordCount (k : Nat) : UInt64 := UInt64.ofNat (min k 536870912)

/-- The instructions that multiply the word on top of the stack by the word count `k`, none for
1. -/
def scaleCode (k : Nat) : Program :=
  if k = 1 then [] else [.constI64 (wordCount k), .mulI64]

/-- The instructions that divide the word on top of the stack by the word count `k`, none for
1. -/
def divCode (k : Nat) : Program :=
  if k = 1 then [] else [.constI64 (wordCount k), .divUI64]

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

def FBinOp.instr : FBinOp → Instruction
  | .add => .f64Add
  | .sub => .f64Sub
  | .mul => .f64Mul
  | .div => .f64Div

def FCmpOp.instr : FCmpOp → Instruction
  | .lt => .f64Lt
  | .le => .f64Le
  | .eq => .f64Eq

/-- The instructions of an operation on one float after the code of its operand.  The negation
subtracts from negative zero, since Talos's `f64.neg` keeps a NaN's payload and flips its sign
while Lean has one NaN. -/
def FUnOp.code (op : FUnOp) (operand : Program) : Program :=
  match op with
  | .sqrt => operand ++ [.f64Sqrt]
  | .abs => operand ++ [.f64Abs]
  | .neg => .f64Const 0x8000000000000000 :: operand ++ [.f64Sub]

/-- The instructions of a conversion of a word to a float after the code of its operand.
`Float.ofBits` reinterprets the word and adds negative zero, which gives the canonical NaN for a
NaN and leaves every other float unchanged. -/
def ToFloat.code : ToFloat → Program
  | .convert => [.f64ConvertI64U]
  | .ofBits => [.f64ReinterpretI64, .f64Const 0x8000000000000000, .f64Add]

def ToWord.instr : ToWord → Instruction
  | .truncate => .i64TruncSatF64U
  | .toBits => .i64ReinterpretF64

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

/-- The local that holds a word of type `ty` at position `p` of a function with `h` positions:
local `p` for an i64, and local `p + h` for an f64.  A function's locals are its parameters, an
i64 local for each further position, and an f64 local for every position. -/
def slotIndex (h p : Nat) : ValueType → Nat
  | .f64 => p + h
  | _ => p

/-- The instructions that push the words of types `tys` at positions `loc` on, in order. -/
def loadCode (h loc : Nat) : List ValueType → Program
  | [] => []
  | ty :: tys => .localGet (slotIndex h loc ty) :: loadCode h (loc + 1) tys

/-- The instructions that store the top words of the stack, of types `tys`, at positions `loc`
on, the top word at the last of them. -/
def storeCode (h loc : Nat) : List ValueType → Program
  | [] => []
  | ty :: tys => storeCode h (loc + 1) tys ++ [.localSet (slotIndex h loc ty)]

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

/-- The instructions that push the address of word `w0 + j` of the array at the address in local
`ptr`, with `w0` in local `w0`. -/
def wordAddrCode (ptr w0 j : Nat) : Program :=
  [.localGet ptr, .localGet w0, .constI64 (UInt64.ofNat (j + 1)), .addI64, .constI64 8, .mulI64,
    .addI64, .wrapI64]

/-- The instructions that push the words `w0 + j` on, of types `tys`, of the array at the address
in local `ptr`, each when the flag in local `flag` is 1, and 0 in its place otherwise. -/
def loadWordsCode (ptr w0 flag : Nat) : Nat → List ValueType → Program
  | _, [] => []
  | j, ty :: tys =>
    [.localGet flag, .wrapI64, .iff 0 1 (wordAddrCode ptr w0 j ++ [.load64 0]) [.constI64 0] []
      [.i64]] ++ ofWordCode ty ++ loadWordsCode ptr w0 flag (j + 1) tys

/-- The instructions that write the words of types `tys` at positions `src` on as the words
`w0 + j` on of the array at the address in local `ptr`. -/
def storeWordsCode (h ptr w0 : Nat) : Nat → Nat → List ValueType → Program
  | _, _, [] => []
  | j, src, ty :: tys =>
    wordAddrCode ptr w0 j ++ .localGet (slotIndex h src ty) :: toWordCode ty ++ [.store64 0] ++
      storeWordsCode h ptr w0 (j + 1) (src + 1) tys

/-- The instructions that push a copy of the value of type `t` whose words positions `src` on
hold: each array copied into a new array, and the other words as they are. -/
def copyCode (h : Nat) : Ty → Nat → Nat → Program
  | .elem e, src, _ => loadCode h src e.types
  | .pair a b, src, base => copyCode h a src base ++ copyCode h b (src + a.width) base
  | .array _, src, base => copyArrayCode src base

/-- The instructions that release the arrays of the owned value of type `t` whose words locals
`src` on hold. -/
def releaseCode : Ty → Nat → Program
  | .elem _, _ => []
  | .pair a b, src => releaseCode a src ++ releaseCode b (src + a.width)
  | .array _, src => [.localGet src, .call 1]

/-- The locals that a copy of a value of type `t` uses: three for each array's copy, and none
for a value without arrays. -/
def Ty.copyScratch (t : Ty) : Nat := if t.scalar then 0 else 3

/-- The locals that turning a borrowed value of type `t` on the stack into an owned copy needs:
its words, and three for the copy of each array. -/
def copyWidth (t : Ty) : Nat := if t.scalar then 0 else t.width + 3

/-- The instructions that turn the value of type `t` on top of the stack, held in mode `source`,
into one held in mode `target`: a borrowed value that must be owned is stored in the locals from
`base` on and copied. -/
def coerceCode (h : Nat) (t : Ty) (source target : Mode) (base : Nat) : Program :=
  if source = .borrowed ∧ target = .owned ∧ t.scalar = false then
    storeCode h base t.types ++ copyCode h t base (base + t.width)
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
def Var.code (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool) {Γ : List Ty}
    {t : Ty} (x : Var Γ t) : Program :=
  if (slots.getD x.index default).mode = .owned ∧ live x.index = true then
    copyCode h t (slots.getD x.index default).loc base
  else loadCode h (slots.getD x.index default).loc t.types

/-- The instructions that push the words of variable `x` as an owned value: its own words when it
is owned and dies, and a copy otherwise. -/
def Var.ownedCode (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool) {Γ : List Ty}
    {t : Ty} (x : Var Γ t) : Program :=
  x.code h slots base live ++ coerceCode h t (slots.getD x.index default).mode .owned base

/-- The instructions that push the byte count of a block for the length in local `total`: the bytes
that the length needs, or twice the capacity in local `cap` when that is more, and at most
`2 ^ 32`. -/
def requestCode (total cap : Nat) : Program :=
  [.localGet total, .constI64 1, .addI64, .constI64 8, .mulI64,
    .localGet cap, .constI64 2, .mulI64, .leUI64,
    .iff 0 1 [.localGet cap, .constI64 2, .mulI64, .constI64 4294967296, .leUI64,
        .iff 0 1 [.localGet cap, .constI64 2, .mulI64] [.constI64 4294967296] [] [.i64]]
      [.localGet total, .constI64 1, .addI64, .constI64 8, .mulI64] [] [.i64]]

/-- The instructions that leave in local `b + 4` the address of an owned array whose first
elements are those of `x`, whose length is `x`'s length plus the word in local `ext`, and whose
block has room for that length.  Local `b` holds `x`'s address, `b + 1` its length, `b + 2` the
new length, `b + 3` the capacity, and `b + 5` the index of the copy.  The code traps at
`unreachable` when the new length is `2 ^ 29` or more.  An owned `x` that dies is extended in its
own block when the block has room, and otherwise copied into a block of at least twice its
capacity, which releases the old block; any other `x` is copied. -/
def Var.roomCode (slots : List Slot) (b : Nat) (live : Nat → Bool) {Γ : List Ty}
    {e : Elem} (x : Var Γ (.array e)) (ext : Nat) : Program :=
  [.localGet (slots.getD x.index default).loc, .localSet b,
    .localGet b, .wrapI64, .load64 0, .localSet (b + 1),
    .localGet (b + 1), .localGet ext, .addI64, .localSet (b + 2),
    .localGet (b + 2), .constI64 536870912, .geUI64, .iff 0 0 [.unreachable] [] [] []] ++
  if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
    [.localGet b, .constI64 32, .subI64, .wrapI64, .load64 0, .localSet (b + 3),
      .localGet (b + 2), .constI64 1, .addI64, .constI64 8, .mulI64, .localGet (b + 3), .leUI64,
      .iff 0 0 [.localGet b, .localSet (b + 4), .localGet (b + 4), .wrapI64, .localGet (b + 2),
          .store64 0]
        (requestCode (b + 2) (b + 3) ++ allocBlockCode (b + 2) (b + 4) ++
          copyIntoCode b (b + 4) (b + 1) (b + 5) ++ [.localGet b, .call 1]) [] []]
  else
    [.localGet (b + 2), .constI64 1, .addI64, .constI64 8, .mulI64] ++
      allocBlockCode (b + 2) (b + 4) ++ copyIntoCode b (b + 4) (b + 1) (b + 5)

/-- The mode that holds both of two values' arrays: owned when either is owned. -/
def Mode.join : Mode → Mode → Mode
  | .borrowed, .borrowed => .borrowed
  | _, _ => .owned

/-- The mode of an expression's value, given the modes of the variables: owned when it holds
arrays that its holder must consume, which a call's result, a built, updated, or extended array, a
moved or copied variable, and a join of an owned value do. -/
def Expr.mode (modes : List Mode) : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Mode
  | _, _, .var x => modes.getD x.index .borrowed
  | _, _, .ite _ thenE elseE => (thenE.mode modes).join (elseE.mode modes)
  | _, _, .letE value body => body.mode (value.mode modes :: modes)
  | _, _, .call (g := g) _ _ => if g.result.scalar then .borrowed else .owned
  | _, _, .build _ _ | _, _, .set _ _ _ | _, _, .push _ _ | _, _, .append _ _ => .owned
  | _, _, .pair first second => (first.mode modes).join (second.mode modes)
  | _, _, .letPair e body => body.mode (e.mode modes :: e.mode modes :: modes)
  | _, _, .loop _ init _ body =>
    (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
  | _, _, _ => .borrowed

/-- The instructions that push the words of an argument at an owned parameter, a variable, as an
owned value. -/
def Expr.ownedCode (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Program
  | _, _, .var x => x.ownedCode h slots base live
  | _, _, _ => []

/-- Whether argument `i` of a call moves its variable into the call: the parameter is owned, and
the argument is an owned variable that is dead after the call and that no other argument with
arrays reads. -/
def callMoves (slots : List Slot) (live : Nat → Bool) {Γ : List Ty} {g : Sig}
    (args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)) (i : Fin g.params.length) :
    Bool :=
  g.mode i == .owned &&
    match (args i).varIndex? with
    | some k => (slots.getD k default).mode == .owned && !live k &&
        !(argsAny fun j => j != i && !(g.params.get j).scalar && (args j).uses k)
    | none => false

/-- The instructions that push the words of a variable or a pair of such expressions, read in
place. -/
def Expr.placeCode (h : Nat) (slots : List Slot) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Program
  | _, _, .var (t := t) x => loadCode h (slots.getD x.index default).loc t.types
  | _, _, .pair first second => first.placeCode h slots ++ second.placeCode h slots
  | _, _, _ => []

/-- The locals that an expression needs from its first free local on: the words of each `letE`
and `letPair` value and of each `ite` result, two for each division or remainder, the count, the
index, and the state of each loop, the position of each read, the count, the address, and the
index of each `build`, with the element's words and the position of its first word, the
position, the value's words, the address, and the position of the first word of each `set`, the
value's words and the scratch of each `push` and `append`, and the locals of each copy, on a path
of the expression.  A call's arguments, a pair's components, and a tuple's components leave their
words on the stack, so they share their locals. -/
def Expr.width : {Γ : List Ty} → {t : Ty} → Expr S Γ t → Nat
  | _, _, .word _ | _, _, .bool _ | _, _, .size _ | _, _, .float _ => 0
  | _, _, .var (t := t) _ => t.copyScratch
  | _, _, .bin op left right => max op.scratch (max left.width right.width)
  | _, _, .cmp _ left right | _, _, .and left right | _, _, .or left right
  | _, _, .fbin _ left right | _, _, .fcmp _ left right =>
    max left.width right.width
  | _, _, .not e | _, _, .funary _ e => e.width
  | _, _, .toFloat _ e => e.width
  | _, _, .toWord _ e => e.width
  | _, _, .ite (t := t) c thenE elseE =>
    max c.width (t.width + max (max thenE.width elseE.width) (copyWidth t))
  | _, _, .letE (s := s) value body => s.width + max value.width body.width
  | _, _, .call (g := g) _ args =>
    argsMax fun i => if g.mode i = .owned then copyWidth (g.params.get i) else (args i).width
  | _, _, .pair (s := s) (t := t) first second =>
    max (max first.width second.width) (max (copyWidth s) (copyWidth t))
  | _, _, .letPair (s := s) (t := t) e body => s.width + t.width + max e.width body.width
  | _, _, .loop (t := t) count init cond body =>
    max count.width (max (1 + max init.width (copyWidth t))
      (2 + t.width + max (max cond.width body.width) (copyWidth t)))
  | _, _, .get _ i => max i.width 2
  | _, _, .build (e := e) count elem => max count.width (3 + max elem.width (e.width + 1))
  | _, _, .set (e := e) _ i v =>
    max i.width (max (1 + v.width) (1 + e.width + copyWidth (.array e)))
  | _, _, .push (e := e) _ v => max v.width (e.width + 7)
  | _, _, .append _ _ => 7
  | _, _, .mk first second => max first.width second.width
  | _, _, .proj _ _ => 0

/-- The instructions that push the words that hold the value of an expression.  Variable `x`
starts at position `(slots.getD x.index default).loc`, the positions from `base` on are free, `h`
is the number of positions, which places each position's f64 local, and `live` gives the
variables live after the expression, which each subexpression receives together with those that
the rest of the expression reads.  Each expression consumes the owned variables
that die in it: a variable moves where it dies and is copied where it stays live, a reader
releases a dying variable it reads, and a branch, a binding, and a loop release the owned
variables that die without a use.  A comparison widens its 32-bit result to a word.  `ite` tests
its condition with `i64.eqz`, so its `if` runs the else branch first, and each branch stores its
words in the locals from `base` on, which the code loads after the `if`: the encoder writes block
types of at most one result.  `letE` stores its value from local `base` on and gives its body the
locals above it, and `letPair` stores its first component from `base` on and its second after
it.  A call pushes its arguments in order, its arrays read in place, and calls the function.  A
loop keeps its count in local `base`, its index in local `base + 1`, and its state from local
`base + 2` on.  Each pass leaves the block when the index reaches the count or when the
condition, which reads the state as a borrowed variable, is false.  The outer variables that the
condition or the body uses stay live through the loop, and the owned ones not live after it are
released there.  `size` loads
the length word at the array's address and divides it by the element's word count `k`.  `get`
keeps the position in local `base`, compares it with the size, keeps the result as a flag in local
`base + 1`, puts the position of the element's first word in local `base`, and loads each of the
element's words under the flag, 0 past the end, turning a float's word into an f64.  `build` keeps
its count in local `base`, traps at `unreachable` when the count's words would be `2 ^ 29` or
more, since the array would not fit in 32-bit memory, allocates the array into local `base + 1`,
and keeps the index in local `base + 2`.  For each index it runs the element's code, stores the
element's words from local `base + 3` on, puts the position of the element's first word after them,
and writes each word; the outer variables that only the element reads stay live through the loop
and are released after it.  `set` keeps the position in local `base` and the value's words from
local `base + 1` on, then takes the array as owned, in local `base + 1 + k`, and writes the
element's words when the position is below the size: an owned array that dies there is updated in
its own block, and any other is copied first.  `push` keeps the value's words from local `base` on
and their count in local `base + k`, and `append` keeps the length of `y` in local `base`; both
take the array `x` with `Var.roomCode`, which gives a block with room for the result, write the new
words, and push the block's address.  `append` releases `y` after the copy when `y` is owned and
dies there.  `mk` pushes its components' words in order, and `proj` loads the words of the
component from the tuple variable's positions. -/
def Expr.code (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    {Γ : List Ty} → {t : Ty} → Expr S Γ t → Program
  | _, _, .word value => [.constI64 value]
  | _, _, .bool value => [.constI64 (boolWord value)]
  | _, _, .float bits =>
    [.f64Const (if Wasm.IEEE64.isNaN bits then Wasm.IEEE64.canonicalNaN else bits)]
  | _, _, .fbin op left right =>
    left.code h slots base (fun i => live i || right.uses i) ++ right.code h slots base live ++
      [op.instr]
  | _, _, .funary op e => op.code (e.code h slots base live)
  | _, _, .fcmp op left right =>
    left.code h slots base (fun i => live i || right.uses i) ++ right.code h slots base live ++
      [op.instr, .extendUI32]
  | _, _, .toFloat op e => e.code h slots base live ++ op.code
  | _, _, .toWord op e => e.code h slots base live ++ [op.instr]
  | _, _, .var x => x.code h slots base live
  | _, _, .bin op left right =>
    left.code h slots base (fun i => live i || right.uses i) ++ right.code h slots base live ++
      op.code base
  | _, _, .cmp op left right =>
    left.code h slots base (fun i => live i || right.uses i) ++ right.code h slots base live ++
      [op.instr, .extendUI32]
  | _, _, .not e => e.code h slots base live ++ [.eqzI64, .extendUI32]
  | _, _, .and left right =>
    left.code h slots base (fun i => live i || right.uses i) ++ right.code h slots base live ++
      [.andI64]
  | _, _, .or left right =>
    left.code h slots base (fun i => live i || right.uses i) ++ right.code h slots base live ++
      [.orI64]
  | Γ, _, .ite (t := t) c thenE elseE =>
    let modes := slots.map Slot.mode
    let mode := (thenE.mode modes).join (elseE.mode modes)
    let mid := fun i => live i || thenE.uses i || elseE.uses i
    c.code h slots base mid ++
      [.eqzI64, .iff 0 0
        (releaseWhere Γ slots (fun i => mid i && !(live i || elseE.uses i)) ++
          elseE.code h slots (base + t.width) live ++
          coerceCode h t (elseE.mode modes) mode (base + t.width) ++ storeCode h base t.types)
        (releaseWhere Γ slots (fun i => mid i && !(live i || thenE.uses i)) ++
          thenE.code h slots (base + t.width) live ++
          coerceCode h t (thenE.mode modes) mode (base + t.width) ++ storeCode h base t.types)
        [] []] ++
      loadCode h base t.types
  | _, _, .letE (s := s) value body =>
    let mode := value.mode (slots.map Slot.mode)
    value.code h slots (base + s.width) (fun i => live i || body.uses (i + 1)) ++
      storeCode h base s.types ++
      (if mode = .owned ∧ body.uses 0 = false then releaseCode s base else []) ++
      body.code h (⟨base, mode⟩ :: slots) (base + s.width) (shift 1 live)
  | Γ, _, .call (g := g) f args =>
    let all := fun i => live i || argsAny fun j => (args j).uses i
    let kept := fun i => all i && !(argsAny fun j => callMoves slots live args j && (args j).uses i)
    argsCode (fun i =>
      if (g.params.get i).scalar then (args i).code h slots base all
      else if g.mode i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++
      [.call f.callIndex] ++
      releaseWhere Γ slots (fun i => kept i && !live i)
  | _, _, .pair (s := s) (t := t) first second =>
    let modes := slots.map Slot.mode
    let mode := (first.mode modes).join (second.mode modes)
    first.code h slots base (fun i => live i || second.uses i) ++
      coerceCode h s (first.mode modes) mode base ++
      second.code h slots base live ++ coerceCode h t (second.mode modes) mode base
  | _, _, .letPair (s := s) (t := t) e body =>
    let mode := e.mode (slots.map Slot.mode)
    e.code h slots (base + s.width + t.width) (fun i => live i || body.uses (i + 2)) ++
      storeCode h (base + s.width) t.types ++ storeCode h base s.types ++
      (if mode = .owned ∧ body.uses 1 = false then releaseCode s base else []) ++
      (if mode = .owned ∧ body.uses 0 = false then releaseCode t (base + s.width) else []) ++
      body.code h (⟨base + s.width, mode⟩ :: ⟨base, mode⟩ :: slots) (base + s.width + t.width)
        (shift 2 live)
  | Γ, _, .loop (t := t) count init cond body =>
    let modes := slots.map Slot.mode
    let mode := (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))
    let all := fun i => live i || cond.uses (i + 1) || body.uses (i + 2)
    count.code h slots base (fun i => all i || init.uses i) ++
      [.localSet base] ++ init.code h slots (base + 1) all ++
      coerceCode h t (init.mode modes) mode (base + 1) ++
      storeCode h (base + 2) t.types ++ [.constI64 0, .localSet (base + 1),
        .block 0 0 [.loop 0 0 ([.localGet (base + 1), .localGet base, .geUI64, .br_if 1] ++
          cond.code h (⟨base + 2, .borrowed⟩ :: slots) (base + 2 + t.width)
            (fun j => j == 0 || shift 1 all j) ++ [.eqzI64, .br_if 1] ++
          (if mode = .owned ∧ body.uses 0 = false then releaseCode t (base + 2) else []) ++
          body.code h (⟨base + 2, mode⟩ :: ⟨base + 1, .borrowed⟩ :: slots)
            (base + 2 + t.width) (shift 2 all) ++
          coerceCode h t (body.mode (mode :: .borrowed :: modes)) mode (base + 2 + t.width) ++
          storeCode h (base + 2) t.types ++
          [.localGet (base + 1), .constI64 1, .addI64, .localSet (base + 1), .br 0]) [] []]
          [] []] ++
      releaseWhere Γ slots (fun i => (cond.uses (i + 1) || body.uses (i + 2)) && !live i) ++
      loadCode h (base + 2) t.types
  | _, _, .size (e := e) x =>
    [.localGet (slots.getD x.index default).loc, .wrapI64, .load64 0] ++ divCode e.width ++
      (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode (.array e) (slots.getD x.index default).loc else [])
  | _, _, .get (e := e) x i =>
    i.code h slots base (fun j => live j || j == x.index) ++
      [.localSet base, .localGet base, .localGet (slots.getD x.index default).loc, .wrapI64,
        .load64 0] ++ divCode e.width ++
      [.ltUI64, .extendUI32, .localSet (base + 1), .localGet base] ++ scaleCode e.width ++
      [.localSet base] ++
      loadWordsCode (slots.getD x.index default).loc base (base + 1) 0 e.types ++
      (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode (.array e) (slots.getD x.index default).loc else [])
  | _, _, .set (e := e) x i v =>
    i.code h slots base (fun j => live j || j == x.index || v.uses j) ++ [.localSet base] ++
      v.code h slots (base + 1) (fun j => live j || j == x.index) ++
      storeCode h (base + 1) e.types ++ x.ownedCode h slots (base + 1 + e.width) live ++
      [.localSet (base + 1 + e.width), .localGet base, .localGet (base + 1 + e.width), .wrapI64,
        .load64 0] ++ divCode e.width ++
      [.ltUI64, .iff 0 0 ([.localGet base] ++ scaleCode e.width ++
          [.localSet (base + 2 + e.width)] ++
          storeWordsCode h (base + 1 + e.width) (base + 2 + e.width) 0 (base + 1) e.types) [] [] [],
        .localGet (base + 1 + e.width)]
  | _, _, .push (e := e) x v =>
    v.code h slots base (fun j => live j || j == x.index) ++ storeCode h base e.types ++
      [.constI64 (wordCount e.width), .localSet (base + e.width)] ++
      x.roomCode slots (base + e.width + 1) live (base + e.width) ++
      storeWordsCode h (base + e.width + 5) (base + e.width + 2) 0 base e.types ++
      [.localGet (base + e.width + 5)]
  | Γ, _, .append x y =>
    [.localGet (slots.getD y.index default).loc, .wrapI64, .load64 0, .localSet base] ++
      x.roomCode slots (base + 1) (fun k => live k || k == y.index) base ++
      [.localGet (base + 5), .localGet (base + 2), .constI64 8, .mulI64, .addI64,
        .localSet (base + 4)] ++
      copyIntoCode (slots.getD y.index default).loc (base + 4) base (base + 6) ++
      releaseWhere Γ slots (fun k => k == y.index && !live k) ++ [.localGet (base + 5)]
  | Γ, _, .build (e := e) count elem =>
    let all := fun i => live i || elem.uses (i + 1)
    count.code h slots base all ++
      [.localSet base, .localGet base,
        .constI64 (UInt64.ofNat ((536870912 + e.width - 1) / e.width)), .geUI64,
        .iff 0 0 [.unreachable] [] [] [], .localGet base] ++ scaleCode e.width ++
      [.localSet (base + 2)] ++ allocArrayCode (base + 2) (base + 1) ++
      [.constI64 0, .localSet (base + 2),
        .block 0 0 [.loop 0 0 ([.localGet (base + 2), .localGet base, .geUI64, .br_if 1] ++
          elem.code h (⟨base + 2, .borrowed⟩ :: slots) (base + 3) (shift 1 all) ++
          storeCode h (base + 3) e.types ++ [.localGet (base + 2)] ++ scaleCode e.width ++
          [.localSet (base + 3 + e.width)] ++
          storeWordsCode h (base + 1) (base + 3 + e.width) 0 (base + 3) e.types ++
          [.localGet (base + 2), .constI64 1, .addI64, .localSet (base + 2), .br 0])
          [] []] [] []] ++
      releaseWhere Γ slots (fun i => elem.uses (i + 1) && !live i) ++ [.localGet (base + 1)]
  | _, _, .mk first second =>
    first.code h slots base (fun i => live i || second.uses i) ++ second.code h slots base live
  | _, _, .proj (e' := e') x p =>
    loadCode h ((slots.getD x.index default).loc + p.offset) e'.types

/-- The slots of parameters of types `ts` for which the modes `ms` were chosen: parameter `i` starts
after the words of the parameters before it. -/
def paramSlots : List Ty → List Mode → Nat → List Slot
  | [], _, _ => []
  | t :: ts, ms, loc =>
    ⟨loc, t.paramMode (ms.headD .borrowed)⟩ :: paramSlots ts ms.tail (loc + t.width)

def Func.type (func : Func S) : FuncType :=
  { params := func.params.flatMap Ty.types
    results := func.result.types }

/-- The instructions that copy each parameter word of type f64, at position `p` on among words of
types `tys`, from its parameter local to the f64 local of its position. -/
def paramCopyCode (h : Nat) : Nat → List ValueType → Program
  | _, [] => []
  | p, .f64 :: tys => [.localGet p, .localSet (p + h)] ++ paramCopyCode h (p + 1) tys
  | p, _ :: tys => paramCopyCode h (p + 1) tys

/-- The positions of a function: its parameters' words and the locals that the body needs. -/
def Func.positions (func : Func S) : Nat :=
  widthSum func.params + func.body.width + copyWidth func.result

/-- The function's code: the words of the arguments are its first positions, and the positions
that the body needs follow them; an i64 local for each of those and an f64 local for every
position follow the parameters.  The code copies the f64 parameter words to their positions'
f64 locals, releases the owned parameters that the body does not use, and runs the body, which
leaves the words of the result on the stack. -/
def Func.function (func : Func S) (typeIdx : Nat) : Wasm.Function :=
  let slots := paramSlots func.params func.modes 0
  let h := func.positions
  { params := func.type.params
    locals := List.replicate (func.body.width + copyWidth func.result) .i64 ++
      List.replicate h .f64
    body := paramCopyCode h 0 (func.params.flatMap Ty.types) ++
      releaseWhere func.params slots (fun i => !func.body.uses i) ++
      func.body.code h slots (widthSum func.params) (fun _ => false) ++
      coerceCode h func.result (func.body.mode (slots.map Slot.mode)) .owned
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
