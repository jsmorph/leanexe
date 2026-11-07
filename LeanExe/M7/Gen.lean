import LeanExe.CallGraph
import LeanExe.M7.Encode

/-!
The code generator of the Cortex-M7 back end: from the module that the verified compiler emits,
the index of a step function, and the words of the step's initial state, a program of the model's
instruction forms whose `main` calls the step forever and performs, after each call, the one
register access that the step requests.  It covers the integer forms of the C path's subset,
calls, and the constructs, and it rejects globals, linear memory, floating point, and every other
form with a message.

The value at operand-stack height `h` lies in a frame slot of 8 bytes, its low word first, and r0
to r7 serve as working registers: an operation loads its operands into r0:r1 and r2:r3, computes in
r0 to r7, and stores its result into the slot of its height.  An `i32` lies in a slot whose high
word is 0, so `extendUI32` emits nothing, `wrapI64` clears the high word, and an `i32` operation
computes on the low words and stores the low word alone.  A function's frame holds, from SP
upward, an outgoing area of one slot for each parameter or result of the largest call in its
body, the slots of the declared locals that the body names, one slot for each operand-stack height
that the body reaches, and the slot of LR, padded to 8 bytes.  A declared local that the body
never names has no slot.  The parameters stay in the caller's outgoing area, parameter `i` at
`SP + F + 8i` for a frame of `F` bytes, and the epilogue copies result `k` from the slot of height
`k` to `SP + F + 8k`.  A call copies its arguments from the slots of their heights into the
outgoing area, branches with `BL`, and copies the results from the outgoing area into the slots
of their heights.  The callee changes no memory from its caller's SP plus 8 times the larger of
its numbers of parameters and results upward.  Every offset from SP lies below 4,096, the reach of
the 12-bit immediates of `LDR`, `STR`, `ADDW`, and `SUBW`, which the generator checks for each
frame as `F + 8 * max p r - 4 ≤ 4095`.

The prologue computes SP less the frame's size into r4, loads the stack's limit into r5, and
branches to a trap stub when r4 lies below r5.  It then lowers SP, stores LR, and clears the slots
of the named declared locals.  A construct carries at most one value, and a branch that carries
one copies the top slot into the slot of the construct's base height.  `br_if` and `if` load the
low word of the condition and compare it with 0.  `divUI64` and `remUI64` test the divisor with
`ORRS`, branch to a trap stub when it is 0, and otherwise call the routine `udivmod64` at the
address `Shared.udivmod`, which takes the dividend in r0:r1 and the divisor in r2:r3, returns the
quotient in r0:r1 and the remainder in r2:r3, changes r4 to r7 and LR, and touches no memory.
Each trap stub is a branch to itself.

The generator places code as it emits it, in units of 4 bytes: `after a n` is the address `n`
units after `a`.  Every form but `BX LR` is 32 bits wide and takes one unit, and a function ends
with two `BX LR`, the second of which never runs, which together take one unit.  Every function
therefore starts at a multiple of 4, and so does each 32-bit instruction of `main` and of the
functions, as in the code of the board's cycle measurements; the code of `udivmod64` follows its
own layout.  Sizes count units, so a function's list of instructions holds one element more than
its size, and a position in the program's list exceeds the instruction's unit count by one for
each function before it.  `instrSize` and `listSize` give a construct's size before its body is
emitted, and every branch is encoded after a check that its offset fits.
-/

namespace LeanExe.M7

open Wasm
open LeanExe.CallGraph

abbrev GenM := Except String

/-- `n` units of 4 bytes after `a`. -/
def after (a : UInt32) (n : Nat) : UInt32 := a + 4 * UInt32.ofNat n

/-- The type of a value that a slot holds: an `i32` or an `i64`. -/
def intType : ValueType → Bool
  | .i32 | .i64 => true
  | _ => false

/-- An offset from SP as the immediate of `LDR`, `STR`, `ADDW`, or `SUBW`. -/
def imm (n : Nat) : GenM (Fin 4096) :=
  if h : n < 4096 then pure ⟨n, h⟩ else throw s!"an offset of {n} bytes beyond 4095"

/-- Loads the two words of the slot at offset `o` from SP into `lo` and `hi`. -/
def ldPair (lo hi : Fin 8) (o : Nat) : GenM (List Instr) := do
  return [.ldrSp lo (← imm o), .ldrSp hi (← imm (o + 4))]

/-- Stores `lo` and `hi` into the two words of the slot at offset `o` from SP. -/
def stPair (lo hi : Fin 8) (o : Nat) : GenM (List Instr) := do
  return [.strSp lo (← imm o), .strSp hi (← imm (o + 4))]

/-- Copies the slot at offset `s` from SP to the slot at offset `d` through r0 and r1. -/
def copySlot (s d : Nat) : GenM (List Instr) := do
  return (← ldPair 0 1 s) ++ (← stPair 0 1 d)

/-- The number of instructions that set a register to the word `w`. -/
def halfSize (w : Nat) : Nat := if w < 65536 then 1 else 2

/-- Sets register `d` to the word `w`, below 2^32, with `MOVW`, and with `MOVT` when `w` has a
nonzero upper half. -/
def movConst (d : Fin 8) (w : Nat) : List Instr :=
  if w < 65536 then [.movwOf d w] else [.movwOf d (w % 65536), .movtOf d (w / 65536)]

/-- The number of instructions that set r0:r1 to `v`. -/
def constSize (v : UInt64) : Nat :=
  halfSize (v.toNat % 4294967296) + halfSize (v.toNat / 4294967296)

/-- Sets r0:r1 to `v`. -/
def movPair (v : UInt64) : List Instr :=
  movConst 0 (v.toNat % 4294967296) ++ movConst 1 (v.toNat / 4294967296)

/-- The byte offset of a branch at `here` to `target`, counted from `here + 4`, when it is even and
lies in `[-2^bits, 2^bits)`. -/
def offsetTo (bits : Nat) (here target : UInt32) : GenM Int := do
  let d : Int := (target.toNat : Int) - ((here.toNat + 4 : Nat) : Int)
  if d % 2 ≠ 0 ∨ d < -((2 ^ bits : Nat) : Int) ∨ ((2 ^ bits : Nat) : Int) ≤ d then
    throw s!"a branch from {here} to {target} beyond {bits + 1} bits"
  return d

/-- `B<c>.W` at `here` to `target`. -/
def bcondAt (c : Fin 14) (here target : UInt32) : GenM Instr := do
  return .bcondTo c (← offsetTo 20 here target)

/-- `B.W` at `here` to `target`. -/
def bAt (here target : UInt32) : GenM Instr := do
  return .bTo (← offsetTo 24 here target)

/-- `BL` at `here` to `target`. -/
def blAt (here target : UInt32) : GenM Instr := do
  return .blTo (← offsetTo 24 here target)

/-- The conditions of `B<c>.W` that the generator uses: EQ, NE, and CC, unsigned lower. -/
def condEQ : Fin 14 := 0
def condNE : Fin 14 := 1
def condCC : Fin 14 := 3

/-- A function's frame: the numbers of its parameters, of the slots of its outgoing area, and of
its operand-stack slots, and the indices of the declared locals that its body names, in order.
Slots are 8 bytes each, from SP upward: the outgoing area, the named declared locals, the operand
stack, and LR. -/
structure Frame where
  params : Nat
  out : Nat
  named : List Nat
  height : Nat

/-- The frame's size in bytes, a multiple of 8. -/
def Frame.size (fr : Frame) : Nat := 8 * (fr.out + fr.named.length + fr.height + 1)

/-- The offset from SP of the slot of LR. -/
def Frame.lrOff (fr : Frame) : Nat := 8 * (fr.out + fr.named.length + fr.height)

/-- The offset from SP of the slot of local `i`: a parameter in the caller's outgoing area, or a
named declared local in the frame. -/
def Frame.localOff (fr : Frame) (i : Nat) : Option Nat :=
  if i < fr.params then some (fr.size + 8 * i)
  else (fr.named.idxOf? i).map fun j => 8 * (fr.out + j)

/-- The offset from SP of the slot of operand-stack height `h`. -/
def Frame.opOff (fr : Frame) (h : Nat) : Option Nat :=
  if h < fr.height then some (8 * (fr.out + fr.named.length + h)) else none

/-- A construct that a branch can target: the target's address, the types of the values that a
branch to it carries, the top first, and the height under those values at the target. -/
structure Ctl where
  target : UInt32
  types : List ValueType
  base : Nat

/-- The number of values that a branch to `t` carries. -/
def Ctl.arity (t : Ctl) : Nat := t.types.length

/-- A table of the functions that calls may name: for each, its entry and the types of its
parameters and of its results. -/
abbrev Table := Nat → Option (UInt32 × List ValueType × List ValueType)

/-- What the functions of a program share: the addresses of the trap stubs for `unreachable`, for
a division by zero, and for a frame that would pass the stack's limit, the entry of `udivmod64`,
and the stack's limit. -/
structure Shared where
  trapUnreachable : UInt32
  trapDiv : UInt32
  trapStack : UInt32
  udivmod : UInt32
  limit : UInt32

/-- What the instructions of one function need: what the program's functions share, the
function's frame, the types of its locals, parameters included, and the table of the functions
that its calls may name. -/
structure Env extends Shared where
  frame : Frame
  localTypes : List ValueType
  callee : Table

/-- The offset from SP of the slot of height `h`. -/
def Env.op (E : Env) (h : Nat) : GenM Nat :=
  match E.frame.opOff h with
  | some o => pure o
  | none => throw s!"height {h} beyond the frame's {E.frame.height} operand slots"

/-- The offset from SP of the slot of local `i`. -/
def Env.loc (E : Env) (i : Nat) : GenM Nat :=
  match E.frame.localOff i with
  | some o => pure o
  | none => throw s!"local {i} without a slot"

/-- The numbers of parameters and results of the functions of the table `callee`. -/
def sigOf (callee : Table) (k : Nat) : Option (Nat × Nat) :=
  (callee k).map fun c => (c.2.1.length, c.2.2.length)

/-- The height of the innermost construct's base, under which its code must not pop. -/
def curBase : List Ctl → Nat
  | [] => 0
  | t :: _ => t.base

/-- The copy of a branch from the operand stack of types `σ`, top first, to `t`, placed at `a`,
when the branch carries a value, and the branch.  A construct carries at most one value, and the
values that the branch carries must have the types of `t`. -/
def branchTo (E : Env) (t : Ctl) (σ : List ValueType) (a : UInt32) : GenM (List Instr) := do
  if σ.length < t.base + t.arity ∨ t.arity > 1 ∨ σ.take t.arity ≠ t.types then
    throw "a branch with fewer values than its target takes, with more than one, or of other types"
  let moves ← if t.arity = 1 then copySlot (← E.op (σ.length - 1)) (← E.op t.base)
    else pure []
  return moves ++ [← bAt (after a moves.length) t.target]

/-- An operation on the two values on top: the loads of the lower into r0:r1 and of the top into
r2:r3, the instructions `ops`, and the store of the pair `res` into the lower's slot, a value of
type `t`. -/
def genBin (E : Env) (ctl : List Ctl) (σ : List ValueType) (ops : List Instr)
    (res : Fin 8 × Fin 8) (t : ValueType) : GenM (List Instr × Option (List ValueType)) := do
  if σ.length < curBase ctl + 2 then throw s!"an operation at height {σ.length}"
  let x ← E.op (σ.length - 2)
  let y ← E.op (σ.length - 1)
  return ((← ldPair 0 1 x) ++ (← ldPair 2 3 y) ++ ops ++ (← stPair res.1 res.2 x),
    some (t :: σ.drop 2))

/-- An operation on the low words of the two `i32`s on top: the loads into r0 and r2, the
instructions `ops`, and the store of r0 into the lower's low word, whose high word stays 0. -/
def genBin32 (E : Env) (ctl : List Ctl) (σ : List ValueType) (ops : List Instr) :
    GenM (List Instr × Option (List ValueType)) := do
  if σ.length < curBase ctl + 2 ∨ σ.take 2 ≠ [.i32, .i32] then
    throw s!"an i32 operation at height {σ.length}"
  let x ← E.op (σ.length - 2)
  let y ← E.op (σ.length - 1)
  return ([.ldrSp 0 (← imm x), .ldrSp 2 (← imm y)] ++ ops ++ [.strSp 0 (← imm x)],
    some (.i32 :: σ.drop 2))

/-- A shift of the `i64` below the top by the low word of the top: the loads into r0:r1 and r2,
the instructions `ops`, and the store of r0:r1. -/
def genShift (E : Env) (ctl : List Ctl) (σ : List ValueType) (ops : List Instr) :
    GenM (List Instr × Option (List ValueType)) := do
  if σ.length < curBase ctl + 2 then throw s!"a shift at height {σ.length}"
  let x ← E.op (σ.length - 2)
  let y ← E.op (σ.length - 1)
  return ((← ldPair 0 1 x) ++ [.ldrSp 2 (← imm y)] ++ ops ++ (← stPair 0 1 x),
    some (.i64 :: σ.drop 2))

/-- The equality of r0:r1 and r2:r3 as 1 or 0 in r0:r1. -/
def eqOps : List Instr :=
  [.eorReg 0 0 2, .eorReg 1 1 3, .orrReg 0 0 0 1, .clz 0 0, .lsrBy 0 0 5, .movImm 1 0]

/-- Whether r0:r1 is at least r2:r3 as unsigned numbers, as 1 or 0 in r0:r1: the carry of the
subtraction. -/
def geOps : List Instr :=
  [.subReg 1 4 0 2, .sbcReg 1 4 1 3, .movImm 0 0, .adcReg 0 0 0, .movImm 1 0]

/-- Whether r0:r1 is at most r2:r3 as unsigned numbers, as 1 or 0 in r0:r1. -/
def leOps : List Instr :=
  [.subReg 1 4 2 0, .sbcReg 1 4 3 1, .movImm 0 0, .adcReg 0 0 0, .movImm 1 0]

/-- r0:r1 shifted left by r2 mod 64, after CompCert's `__compcert_i64_shl`: a register shift by 32
or more gives 0, so the cross terms of `32 - n` and `n - 32` are exact for every `n`. -/
def shlOps : List Instr :=
  [.andImm 2 2 63, .movImm 3 32, .subReg 0 3 3 2, .lslReg 1 1 2, .lsrReg 3 0 3, .orrReg 0 1 1 3,
    .subImm 3 2 32, .lslReg 3 0 3, .orrReg 0 1 1 3, .lslReg 0 0 2]

/-- r0:r1 shifted right by r2 mod 64, the mirror image of `shlOps`. -/
def shrOps : List Instr :=
  [.andImm 2 2 63, .movImm 3 32, .subReg 0 3 3 2, .lsrReg 0 0 2, .lslReg 3 1 3, .orrReg 0 0 0 3,
    .subImm 3 2 32, .lsrReg 3 1 3, .orrReg 0 0 0 3, .lsrReg 1 1 2]

/-- A division of the `i64` below the top by the top, placed at `a`: the loads of the dividend into
r0:r1 and of the divisor into r2:r3, the test of the divisor and the branch to `trapDiv` when it is
0, the call of `udivmod64`, and the store of the pair `res`, r0:r1 for the quotient or r2:r3 for
the remainder. -/
def genDiv (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt32) (res : Fin 8 × Fin 8) :
    GenM (List Instr × Option (List ValueType)) := do
  if σ.length < curBase ctl + 2 then throw s!"a division at height {σ.length}"
  let x ← E.op (σ.length - 2)
  let y ← E.op (σ.length - 1)
  return ((← ldPair 0 1 x) ++ (← ldPair 2 3 y) ++ [.orrReg 1 4 2 3,
    ← bcondAt condEQ (after a 5) E.trapDiv, ← blAt (after a 6) E.udivmod] ++
    (← stPair res.1 res.2 x), some (.i64 :: σ.drop 2))

mutual
/-- The number of units of `ins` at height `h`, under constructs whose branches carry `ar`
values, the innermost first, for calls of functions whose numbers of parameters and results `sig`
gives, and the height after it, or `none` when the code after it is unreachable. -/
def instrSize (sig : Nat → Option (Nat × Nat)) (ar : List Nat) (h : Nat) :
    Instruction → Nat × Option Nat
  | .localGet _ => (4, some (h + 1))
  | .localSet _ => (4, some (h - 1))
  | .localTee _ => (4, some h)
  | .constI64 v => (constSize v + 2, some (h + 1))
  | .const v => (constSize v.toUInt64 + 2, some (h + 1))
  | .eqI64 => (12, some (h - 1))
  | .neI64 => (13, some (h - 1))
  | .eq => (6, some (h - 1))
  | .ltUI64 => (12, some (h - 1))
  | .leUI64 | .geUI64 => (11, some (h - 1))
  | .eqzI64 => (8, some h)
  | .eqz => (4, some h)
  | .addI64 | .subI64 | .andI64 | .orI64 | .xorI64 => (8, some (h - 1))
  | .mulI64 => (9, some (h - 1))
  | .and => (4, some (h - 1))
  | .shlI64 | .shrUI64 => (15, some (h - 1))
  | .wrapI64 => (2, some h)
  | .extendUI32 => (0, some h)
  | .divUI64 | .remUI64 => (9, some (h - 1))
  | .unreachable => (1, none)
  | .br n => (4 * ar[n]?.getD 0 + 1, none)
  | .br_if n => (if ar[n]?.getD 0 = 0 then 3 else 4 * ar[n]?.getD 0 + 4, some (h - 1))
  | .ret => (4 * ar.getLast?.getD 0 + 1, none)
  | .block _ ra body _ _ => ((listSize sig (ra :: ar) h body).1, some (h + ra))
  | .loop _ ra body _ _ => ((listSize sig (0 :: ar) h body).1, some (h + ra))
  | .iff _ ra thn els _ _ =>
      ((listSize sig (ra :: ar) (h - 1) thn).1 + (listSize sig (ra :: ar) (h - 1) els).1 + 4,
        some (h - 1 + ra))
  | .call k =>
      match sig k with
      | some (p, r) => (4 * p + 1 + 4 * r, some (h - p + r))
      | none => (0, none)
  | _ => (0, none)

/-- The number of units of `is` at height `h` and the height after them, or `none` when their end
is unreachable. -/
def listSize (sig : Nat → Option (Nat × Nat)) (ar : List Nat) (h : Nat) :
    List Instruction → Nat × Option Nat
  | [] => (0, some h)
  | i :: rest =>
      match (instrSize sig ar h i).2 with
      | none => ((instrSize sig ar h i).1, none)
      | some h' => ((instrSize sig ar h i).1 + (listSize sig ar h' rest).1,
          (listSize sig ar h' rest).2)
end

mutual
/-- The instructions of `ins` placed at `a`, on the operand stack of types `σ`, top first, under
the constructs `ctl`, and the types after it, or `none` when the code after it is unreachable. -/
def genInstr (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt32) :
    Instruction → GenM (List Instr × Option (List ValueType))
  | .localGet i => do
      match E.localTypes[i]? with
      | some t => return (← copySlot (← E.loc i) (← E.op σ.length), some (t :: σ))
      | none => throw s!"local {i} of {E.localTypes.length}"
  | .localSet i => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ E.localTypes[i]? then
        throw s!"local.set {i} at height {σ.length}"
      return (← copySlot (← E.op (σ.length - 1)) (← E.loc i), some σ.tail)
  | .localTee i => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ E.localTypes[i]? then
        throw s!"local.tee {i} at height {σ.length}"
      return (← copySlot (← E.op (σ.length - 1)) (← E.loc i), some σ)
  | .constI64 v => do return (movPair v ++ (← stPair 0 1 (← E.op σ.length)), some (.i64 :: σ))
  | .const v => do
      return (movPair v.toUInt64 ++ (← stPair 0 1 (← E.op σ.length)), some (.i32 :: σ))
  | .eqI64 => genBin E ctl σ eqOps (0, 1) .i32
  | .neI64 => genBin E ctl σ (eqOps ++ [.eorImm 0 0 1]) (0, 1) .i32
  | .eq => genBin32 E ctl σ [.eorReg 0 0 2, .clz 0 0, .lsrBy 0 0 5]
  | .ltUI64 => genBin E ctl σ (geOps ++ [.eorImm 0 0 1]) (0, 1) .i32
  | .leUI64 => genBin E ctl σ leOps (0, 1) .i32
  | .geUI64 => genBin E ctl σ geOps (0, 1) .i32
  | .eqzI64 => do
      if σ.length < curBase ctl + 1 then throw s!"eqz at height {σ.length}"
      let x ← E.op (σ.length - 1)
      return ((← ldPair 0 1 x) ++ [.orrReg 0 0 0 1, .clz 0 0, .lsrBy 0 0 5, .movImm 1 0] ++
        (← stPair 0 1 x), some (.i32 :: σ.tail))
  | .eqz => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ some .i32 then
        throw s!"eqz at height {σ.length}"
      let x ← E.op (σ.length - 1)
      return ([.ldrSp 0 (← imm x), .clz 0 0, .lsrBy 0 0 5, .strSp 0 (← imm x)],
        some (.i32 :: σ.tail))
  | .addI64 => genBin E ctl σ [.addReg 1 0 0 2 0 0, .adcReg 1 1 3] (0, 1) .i64
  | .subI64 => genBin E ctl σ [.subReg 1 0 0 2, .sbcReg 0 1 1 3] (0, 1) .i64
  | .mulI64 =>
      genBin E ctl σ [.umull 4 5 0 2 (by decide), .mla 5 0 3 5, .mla 5 1 2 5] (4, 5) .i64
  | .andI64 => genBin E ctl σ [.andReg 0 0 2, .andReg 1 1 3] (0, 1) .i64
  | .and => genBin32 E ctl σ [.andReg 0 0 2]
  | .orI64 => genBin E ctl σ [.orrReg 0 0 0 2, .orrReg 0 1 1 3] (0, 1) .i64
  | .xorI64 => genBin E ctl σ [.eorReg 0 0 2, .eorReg 1 1 3] (0, 1) .i64
  | .shlI64 => genShift E ctl σ shlOps
  | .shrUI64 => genShift E ctl σ shrOps
  | .wrapI64 => do
      if σ.length < curBase ctl + 1 then throw s!"wrap at height {σ.length}"
      return ([.movImm 0 0, .strSp 0 (← imm ((← E.op (σ.length - 1)) + 4))],
        some (.i32 :: σ.tail))
  | .extendUI32 => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ some .i32 then
        throw s!"extend at height {σ.length}"
      return ([], some (.i64 :: σ.tail))
  | .divUI64 => genDiv E ctl σ a (0, 1)
  | .remUI64 => genDiv E ctl σ a (2, 3)
  | .unreachable => do return ([← bAt a E.trapUnreachable], none)
  | .br n => do
      match ctl[n]? with
      | some t => return (← branchTo E t σ a, none)
      | none => throw s!"br {n} under {ctl.length} constructs"
  | .br_if n => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ some .i32 then
        throw s!"br_if at height {σ.length}"
      match ctl[n]? with
      | some t =>
          let c ← imm (← E.op (σ.length - 1))
          if t.arity = 0 then
            return ([.ldrSp 0 c, .cmpImm 0 0, ← bcondAt condNE (after a 2) t.target],
              some σ.tail)
          let skip := after a (4 * t.arity + 4)
          return ([.ldrSp 0 c, .cmpImm 0 0, ← bcondAt condEQ (after a 2) skip] ++
            (← branchTo E t σ.tail (after a 3)), some σ.tail)
      | none => throw s!"br_if {n} under {ctl.length} constructs"
  | .ret => do
      match ctl.getLast? with
      | some t => return (← branchTo E t σ a, none)
      | none => throw "ret outside a function"
  | .block pa ra body _ rts => do
      if pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra then
        throw "a block with parameters, more than one result, or results without their types"
      let n := (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) σ.length body).1
      let inner := { target := after a n, types := rts.reverse, base := σ.length } :: ctl
      let (code, fin) ← genList E inner σ a body
      if fin.any (· ≠ rts.reverse ++ σ) then throw "a block that ends with other types"
      return (code, some (rts.reverse ++ σ))
  | .loop pa ra body _ rts => do
      if pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra then
        throw "a loop with parameters, more than one result, or results without their types"
      let inner := { target := a, types := [], base := σ.length } :: ctl
      let (code, fin) ← genList E inner σ a body
      if fin.any (· ≠ rts.reverse ++ σ) then throw "a loop that ends with other types"
      return (code, some (rts.reverse ++ σ))
  | .iff pa ra thn els _ rts => do
      if pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra ∨ σ.length < curBase ctl + 1 ∨
          σ.head? ≠ some .i32 then
        throw "an if with parameters, more than one result, results without types, or no condition"
      let c ← imm (← E.op (σ.length - 1))
      let ar := ra :: ctl.map (·.arity)
      let aB := after a (3 + (listSize (sigOf E.callee) ar (σ.length - 1) thn).1)
      let aElse := after aB 1
      let aEnd := after aElse (listSize (sigOf E.callee) ar (σ.length - 1) els).1
      let inner := { target := aEnd, types := rts.reverse, base := σ.length - 1 } :: ctl
      let (ti, ta) ← genList E inner σ.tail (after a 3) thn
      let (ei, ea) ← genList E inner σ.tail aElse els
      if ta.any (· ≠ rts.reverse ++ σ.tail) ∨ ea.any (· ≠ rts.reverse ++ σ.tail) then
        throw "an if whose branches end with other types"
      return ([.ldrSp 0 c, .cmpImm 0 0, ← bcondAt condEQ (after a 2) aElse] ++ ti ++
        [← bAt aB aEnd] ++ ei, some (rts.reverse ++ σ.tail))
  | .call k => do
      match E.callee k with
      | none => throw s!"a call of function {k}, which the program lacks"
      | some (target, ps, rs) =>
          let h := σ.length
          let p := ps.length
          if h < curBase ctl + p ∨ E.frame.out < max p rs.length ∨ σ.take p ≠ ps.reverse then
            throw s!"a call of function {k} at height {h}"
          let args ← (List.range p).mapM fun i => do copySlot (← E.op (h - p + i)) (8 * i)
          let res ← (List.range rs.length).mapM fun j => do
            copySlot (8 * j) (← E.op (h - p + j))
          return (args.flatten ++ [← blAt (after a (4 * p)) target] ++ res.flatten,
            some (rs.reverse ++ σ.drop p))
  | i => throw s!"the form {repr i} lies outside the generator's forms"

/-- The instructions of `is` placed at `a`, on the operand stack of types `σ` under the
constructs `ctl`, and the types after them, or `none` when their end is unreachable. -/
def genList (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt32) :
    List Instruction → GenM (List Instr × Option (List ValueType))
  | [] => return ([], some σ)
  | i :: rest => do
      let (c1, fin) ← genInstr E ctl σ a i
      match fin with
      | none => return (c1, none)
      | some σ' =>
          let (c2, fin') ← genList E ctl σ' (after a c1.length) rest
          return (c1 ++ c2, fin')
end

/-- The height after `ins` at height `h`, or `none` when the code after it is unreachable, as
`instrSize` gives it. -/
def heightAfter (sig : Nat → Option (Nat × Nat)) (h : Nat) : Instruction → Option Nat
  | .block _ ra _ _ _ | .loop _ ra _ _ _ => some (h + ra)
  | .iff _ ra _ _ _ _ => some (h - 1 + ra)
  | i => (instrSize sig [] h i).2

mutual
/-- The largest operand-stack height that `ins` reaches from height `h`. -/
def instrPeak (sig : Nat → Option (Nat × Nat)) (h : Nat) : Instruction → Nat
  | .block _ _ body _ _ | .loop _ _ body _ _ => listPeak sig h body
  | .iff _ _ thn els _ _ => max h (max (listPeak sig (h - 1) thn) (listPeak sig (h - 1) els))
  | i => max h ((heightAfter sig h i).getD h)

/-- The largest operand-stack height that `is` reaches from height `h`. -/
def listPeak (sig : Nat → Option (Nat × Nat)) (h : Nat) : List Instruction → Nat
  | [] => h
  | i :: rest =>
      match heightAfter sig h i with
      | none => instrPeak sig h i
      | some h' => max (instrPeak sig h i) (listPeak sig h' rest)
end

mutual
/-- The locals that `ins` names. -/
def instrLocals : Instruction → List Nat
  | .localGet i | .localSet i | .localTee i => [i]
  | .block _ _ body _ _ | .loop _ _ body _ _ => listLocals body
  | .iff _ _ thn els _ _ => listLocals thn ++ listLocals els
  | _ => []

/-- The locals that the instructions `is` name. -/
def listLocals : List Instruction → List Nat
  | [] => []
  | i :: rest => instrLocals i ++ listLocals rest
end

/-- The frame of the function `f`, whose calls name functions whose numbers of parameters and
results `sig` gives. -/
def frameOf (sig : Nat → Option (Nat × Nat)) (f : Function) : Frame :=
  let p := f.params.length
  let names := listLocals f.body
  { params := p
    out := (callsIn f.body).foldl (fun acc k => max acc ((sig k).elim 0 fun (q, r) => max q r)) 0
    named := (List.range f.locals.length).filterMap fun j =>
      if names.contains (p + j) then some (p + j) else none
    height := max f.results.length (listPeak sig 0 f.body) }

/-- The number of units of the clearing of the named declared locals of the frame `fr`. -/
def clearSize (fr : Frame) : Nat := if fr.named = [] then 0 else 1 + 2 * fr.named.length

/-- The number of units of the prologue. -/
def prologueSize : Nat := 7

/-- The number of units of the epilogue of a function with `r` results. -/
def epilogueSize (r : Nat) : Nat := 4 * r + 3

/-- The number of units of the function `f`, whose calls name functions whose numbers of
parameters and results `sig` gives. -/
def functionSize (sig : Nat → Option (Nat × Nat)) (f : Function) : Nat :=
  prologueSize + clearSize (frameOf sig f) + (listSize sig [f.results.length] 0 f.body).1 +
    epilogueSize f.results.length

/-- The instructions of the function `f` placed at `entry`.  The prologue sets r4 to SP less the
frame's size, compares it with the stack's limit in r5, and branches to `trapStack` when it lies
below; it then lowers SP, stores LR, and clears the slots of the named declared locals.  The body
follows, then the epilogue, which copies the results to the caller's outgoing area, reloads LR,
raises SP, and returns.  Its calls name the functions of `callee`. -/
def genFunction (callee : Table) (S : Shared) (entry : UInt32) (f : Function) :
    GenM (List Instr) := do
  let p := f.params.length
  let r := f.results.length
  let fr := frameOf (sigOf callee) f
  let types := f.params ++ f.locals
  if !(f.params ++ f.results).all intType then
    throw "a parameter or result that is neither an i32 nor an i64"
  if !fr.named.all fun i => (types[i]?.map intType).getD false then
    throw "a named local that is neither an i32 nor an i64"
  let F := fr.size
  if 4096 ≤ F ∨ 4096 < F + 8 * max p r then
    throw s!"a frame of {F} bytes whose offsets reach {F + 8 * max p r - 4}"
  let E : Env := { toShared := S, frame := fr, localTypes := types, callee := callee }
  let lim := S.limit.toNat
  let prologue := [.subwSpOf 4 F, .movwOf 5 (lim % 65536), .movtOf 5 (lim / 65536), .cmpReg 4 5,
    ← bcondAt condCC (after entry 4) S.trapStack, .subwSpSpOf F, .strLr (← imm fr.lrOff)]
  let clear ← if fr.named = [] then pure []
    else do pure (.movImm 0 0 :: (← fr.named.mapM fun i => do stPair 0 0 (← E.loc i)).flatten)
  let bodyA := after entry (prologueSize + clear.length)
  let epilogueA := after bodyA (listSize (sigOf callee) [r] 0 f.body).1
  let (body, fin) ←
    genList E [{ target := epilogueA, types := f.results.reverse, base := 0 }] [] bodyA f.body
  if fin.any (· ≠ f.results.reverse) then throw "a function body that ends with other types"
  let results ← (List.range r).mapM fun k => do copySlot (← E.op k) (F + 8 * k)
  return prologue ++ clear ++ body ++ results.flatten ++
    [.ldrLr (← imm fr.lrOff), .addwSpSpOf F, .bxLr, .bxLr]

/-- The number of units of `main`'s start for the initial state `s0`: the frame, the state's
words, and the last value. -/
def mainStart (s0 : List UInt64) : Nat := 1 + (s0.map fun w => constSize w + 2).sum + 3

/-- The number of units of `main` for the initial state `s0`. -/
def mainSize (s0 : List UInt64) : Nat := mainStart s0 + 21

/-- `main` placed at `a` for the step at `step` from the state of the words `s0`, with the device
window from `dev`.  It lowers SP by the outgoing area of the step's `n + 1` parameters and results,
for the `n` words of `s0`, and stores the state's words into slots 0 to `n - 1` and 0 into slot
`n`.  Each window calls the step, which leaves the new state in slots 0 to `n - 1` and the request
in slot `n`, and performs the request: the address `dev + 4 * ((q >> 32) & 65535)` from the high
word, and bit 63 set for a write of the low word, after which slot `n` holds 0, or clear for a read,
whose value slot `n` then holds, zero-extended.  The loop's head lies at `mainStart s0` units. -/
def genMain (a step dev : UInt32) (s0 : List UInt64) : GenM (List Instr) := do
  let n := s0.length
  let area ← imm (8 * (n + 1))
  let q ← imm (8 * n)
  let qh ← imm (8 * n + 4)
  let words ← s0.zipIdx.mapM fun (w, i) => do pure (movPair w ++ (← stPair 0 1 (8 * i)))
  let start := [.subwSpSpOf area.val] ++ words.flatten ++
    [.movImm 0 0, .strSp 0 q, .strSp 0 qh]
  let head := after a start.length
  let rd := after head 10
  let wr := after rd 5
  let window := [← blAt head step, .ldrSp 1 qh, .lslBy 2 1 16, .lsrBy 2 2 16,
    .movwOf 3 (dev.toNat % 65536), .movtOf 3 (dev.toNat / 65536), .addLsl 0 3 3 2 2,
    .lsrBy 4 1 31, .cmpImm 4 0, ← bcondAt condNE (after head 9) wr]
  let read := [.ldr 0 3 0, .strSp 0 q, .movImm 0 0, .strSp 0 qh, ← bAt (after rd 4) head]
  let write := [.ldrSp 0 q, .str 0 3 0, .movImm 0 0, .strSp 0 q, .strSp 0 qh,
    ← bAt (after wr 5) head]
  return start ++ window ++ read ++ write

/-- The entries of the functions of `fs`, laid out one after another from `a`, with the types of
their parameters and results, by index. -/
def entriesFrom (sig : Nat → Option (Nat × Nat)) :
    UInt32 → List (Nat × Function) → List (Nat × UInt32 × List ValueType × List ValueType)
  | _, [] => []
  | a, (j, f) :: rest =>
      (j, a, f.params, f.results) :: entriesFrom sig (after a (functionSize sig f)) rest

/-- The address after the functions of `fs`, laid out one after another from `a`. -/
def endOf (sig : Nat → Option (Nat × Nat)) : UInt32 → List (Nat × Function) → UInt32
  | a, [] => a
  | a, (_, f) :: rest => endOf sig (after a (functionSize sig f)) rest

/-- The table of the functions of `entries` that `targets` names. -/
def tableOf (targets : List Nat)
    (entries : List (Nat × UInt32 × List ValueType × List ValueType)) : Table :=
  fun j => if j ∈ targets then (entries.find? (·.1 = j)).map (·.2) else none

/-- The number of halfwords of the instruction `i`. -/
def Instr.halfwords : Instr → Nat
  | .bxLr => 1
  | _ => 2

/-- The number of halfwords of the instructions `is`. -/
def halfwordsOf (is : List Instr) : Nat := (is.map Instr.halfwords).sum

/-- The instructions of the functions of `fs`, one after another from `a`, each checked against
its size. -/
def genFunctions (callee : Table) (S : Shared) :
    UInt32 → List (Nat × Function) → GenM (List Instr)
  | _, [] => pure []
  | a, (j, f) :: rest => do
      let is ← genFunction callee S a f
      let n := functionSize (sigOf callee) f
      if halfwordsOf is ≠ 2 * n then
        throw s!"function {j}: {halfwordsOf is} halfwords against a size of {n} units"
      return is ++ (← genFunctions callee S (after a n) rest)

/-- The program that runs function `k` of `m` as a step from the state of the words `s0`, placed
at `base`, with the stack's limit `limit`, the device window from `dev`, and the code `div` of
`udivmod64`: `main`, the functions that calls reach from function `k`, `k` first, the trap stubs
of `unreachable`, of a division by zero, and of the stack, each a branch to itself, and `div`.
Function `k` takes and returns `s0.length + 1` values of type `i64`. -/
def genProgram (m : Module) (k : Nat) (s0 : List UInt64) (base limit dev : UInt32)
    (div : List Instr) : GenM (List Instr) := do
  let fs ← (reachFrom m k).mapM (funcOf m)
  let targets := callTargets m k
  let sig := sigIn targets fs
  let first := after base (mainSize s0)
  let entries := entriesFrom sig first fs
  let callee := tableOf targets entries
  let traps := endOf sig first fs
  let entry ← match (entries.find? (·.1 = k)).map (·.2) with
    | some (e, ps, rs) =>
        let w := List.replicate (s0.length + 1) ValueType.i64
        if ps = w ∧ rs = w then pure e
        else throw s!"function {k} does not take and return {s0.length + 1} i64s"
    | none => throw s!"no function {k}"
  let main ← genMain base entry dev s0
  if main.length ≠ mainSize s0 then throw s!"main: {main.length} units against {mainSize s0}"
  let S : Shared :=
    { trapUnreachable := traps, trapDiv := after traps 1, trapStack := after traps 2,
      udivmod := after traps 3, limit }
  let fns ← genFunctions callee S first fs
  return main ++ fns ++ [.bTo (-4), .bTo (-4), .bTo (-4)] ++ div

end LeanExe.M7
