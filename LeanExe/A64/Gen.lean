import Interpreter.Wasm.Syntax
import LeanExe.A64.Encode

/-!
The code generator of the AArch64 back end: from a function of a module of the verified
compiler and its arguments, a bare-metal program of the model's instruction forms whose `main`
calls the function, writes the eight bytes of its result to the UART, and returns 0 to the
startup code of `tools/baremetal/start.S`.  It covers the Wasm forms of GCD's loop, the integer
comparisons and operations of the C path's subset, calls, globals, and the 64-bit loads and stores
of linear memory, and it rejects every other form with a message.

The operand stack's height and types are fixed at every reachable instruction, so the value at
height `h` lies in the register `opReg h`, X0 to X15 and then X19 to X28.  The generator tracks the
types and checks the types of the values that a `local.set`, a branch, and a call receive against
the declared types.  An `i32` lies there zero-extended, so `extendUI32` emits nothing, `wrapI64` is
a 32-bit `ORR`, and an `i32` comparison or `and` is the 64-bit one.  X16 is the scratch register of
`remUI64`, of the prologue, and of the memory's instructions, and X29 is a second one of
`memory.grow`.  X17 holds the address of the area of the module's store: the memory's size less 8,
the globals, and the memory's bytes, which a load or store reaches after a check of its bounds.  A
function keeps its parameters and locals in a frame at `SP` of 8 bytes each, followed by 26 spill
slots and the slot of the return address, a multiple of 16 bytes in all.  Its prologue checks that
the frame fits above the stack's limit, which X18 holds, reserves the frame, stores the parameters
into it from the registers of the heights 0 upward, and clears the other locals.  A call spills the
operand registers below its arguments to the spill slots, moves the arguments into the registers of
the heights 0 upward, branches with `BL`, moves the results from those registers into the registers
of their heights, and reloads the spilled registers.  The callee may change every register but SP,
X17, and X18, and it changes no memory from its caller's SP upward.  A construct carries at most one
value, and a branch to one moves the value that it carries, if any, into the register of the
construct's base height with one `ORR` and branches to the construct's target: the end of a `block`
or an `iff`, the start of a `loop`, or the epilogue for the function itself, which also serves
`ret`.  The results lie at the heights from 0, in the registers of those heights, when the epilogue
releases the frame and returns.  Code after a `br`, a `ret`, or `unreachable` in the same list is
unreachable, and the generator emits nothing for it, while the code after a construct is reachable,
as Wasm's typing has it.  No instruction may pop below the base height of its innermost construct,
`curBase`, as valid Wasm never does: Talos runs a construct's body on the whole operand stack and
restores the values below the construct afterwards, which the registers of those heights would not
follow.  A trap branches to a stub that sets X0 to the trap's code of `LeanExe.Native.trapCode`, 1,
2, or 3, or to 4 for an overflow of the stack, and branches to the program's exit word, which the
image fills with a branch to `lx_exit` of the startup code.

The generator places code as it emits it: each function takes the address of its first
instruction, and `instrSize` and `listSize` give the number of instructions of a construct
without addresses, so a construct's end is known before its body is emitted.  Every branch is
encoded with its offset after a check that the offset fits.
-/

namespace LeanExe.A64

open Wasm

/-- The registers of the operand stack's heights. -/
def opRegs : List Nat := List.range 16 ++ (List.range 10).map (· + 19)

/-- The register of height `k`, which `opReg k` gives for the 26 heights that have one. -/
def regOf (k : Nat) : Fin 32 := ⟨opRegs.getD k 0 % 32, Nat.mod_lt _ (by decide)⟩

/-- The scratch register. -/
def scratch : Fin 32 := 16

/-- The number of a frame's slots between the locals and the return address, which hold the
operand registers that a call spills. -/
def spillSlots : Nat := 26

abbrev GenM := Except String

/-- The register of height `h`. -/
def opReg (h : Nat) : GenM (Fin 32) :=
  match opRegs[h]? with
  | some r => pure ⟨r % 32, Nat.mod_lt _ (by decide)⟩
  | none => throw s!"an operand stack deeper than {opRegs.length} values"

/-- Bits `16 * k` to `16 * k + 15` of `v`. -/
def half (v : UInt64) (k : Nat) : Fin 65536 :=
  ⟨v.toNat / 65536 ^ k % 65536, Nat.mod_lt _ (by decide)⟩

/-- Sets register `d` to `v` with `MOVZ` and three `MOVK`. -/
def movImm (d : Fin 32) (v : UInt64) : List Instr :=
  [.movz d (half v 0) 0, .movk d (half v 1) 1, .movk d (half v 2) 2, .movk d (half v 3) 3]

/-- Copies register `s` to register `d`. -/
def mov (d s : Fin 32) : Instr := .orrReg d 31 s

/-- The frame slot of local `i`, as the scaled offset of `LDR` and `STR`. -/
def slotOf (i : Nat) : GenM (Fin 4096) :=
  if h : i < 4096 then pure ⟨i, h⟩ else throw s!"local {i} lies beyond the frame's reach"

/-- The field of `bits` bits of a branch from `here` to `target`, when the offset fits. -/
def branchField (bits : Nat) (here target : UInt64) : GenM Nat := do
  let d := Int.ofNat target.toNat - Int.ofNat here.toNat
  if d % 4 ≠ 0 ∨ d / 4 < -(2 ^ (bits - 1)) ∨ d / 4 ≥ 2 ^ (bits - 1) then
    throw s!"a branch from {here} to {target} beyond {bits} bits"
  return (d / 4 % (2 ^ bits : Int)).toNat

/-- The field of `B` or `BL` from `here` to `target`. -/
def bField (here target : UInt64) : GenM (Fin 67108864) := do
  return ⟨(← branchField 26 here target) % 67108864, Nat.mod_lt _ (by decide)⟩

/-- The field of `CBZ` or `CBNZ` from `here` to `target`. -/
def cbField (here target : UInt64) : GenM (Fin 524288) := do
  return ⟨(← branchField 19 here target) % 524288, Nat.mod_lt _ (by decide)⟩

/-- `n` instructions after `a`. -/
def after (a : UInt64) (n : Nat) : UInt64 := a + 4 * UInt64.ofNat n

/-- A construct that a branch can target: the target's address, the types of the values that a
branch to it carries, the top first, and the height under those values at the target. -/
structure Ctl where
  target : UInt64
  types : List ValueType
  base : Nat

/-- The number of values that a branch to `t` carries. -/
def Ctl.arity (t : Ctl) : Nat := t.types.length

/-- A table of the functions that calls may name: for each, its entry and the types of its
parameters and of its results. -/
abbrev Table := Nat → Option (UInt64 × List ValueType × List ValueType)

/-- What the functions of a program share: the addresses of the trap stubs for `unreachable`, for
an access outside the memory, for a division by zero, and for a stack that a frame would
overflow, the memory's cap in pages, and the types of the globals. -/
structure Shared where
  trapUnreachable : UInt64
  trapBounds : UInt64
  trapDiv : UInt64
  trapStack : UInt64
  cap : Nat
  globalTypes : List ValueType

/-- What the instructions of one function need: what the program's functions share, the types of
the function's locals, parameters included, and the table of the functions that its calls may
name. -/
structure Env extends Shared where
  localTypes : List ValueType
  callee : Table

/-- The number of the locals of `E`, parameters included. -/
def Env.locals (E : Env) : Nat := E.localTypes.length

/-- The numbers of parameters and results of the functions of the table `callee`. -/
def sigOf (callee : Table) (k : Nat) : Option (Nat × Nat) :=
  (callee k).map fun c => (c.2.1.length, c.2.2.length)

/-- The height of the innermost construct's base, under which its code must not pop. -/
def curBase : List Ctl → Nat
  | [] => 0
  | t :: _ => t.base

/-- The move of a branch from the operand stack of types `σ`, top first, to `t`, placed at `a`,
when the branch carries a value, and the branch.  A construct carries at most one value, as the
subset of `LeanExe/Native/Subset.lean` requires, and the values that the branch carries must have
the types of `t`. -/
def branchTo (t : Ctl) (σ : List ValueType) (a : UInt64) : GenM (List Instr) := do
  if σ.length < t.base + t.arity ∨ t.arity > 1 ∨ σ.take t.arity ≠ t.types then
    throw "a branch with fewer values than its target takes, with more than one, or of other types"
  let moves ← if t.arity = 1 then do pure [mov (← opReg t.base) (← opReg (σ.length - 1))]
    else pure []
  return moves ++ [.b (← bField (after a t.arity) t.target)]

/-- A comparison of the two values on top, which `SUBS` and `CSINC` with the condition `c`, the
inverse of the comparison's, replace by 1 or 0, an `i32`. -/
def genCmp (ctl : List Ctl) (σ : List ValueType) (c : Fin 16) :
    GenM (List Instr × Option (List ValueType)) := do
  if σ.length < curBase ctl + 2 then throw s!"a comparison at height {σ.length}"
  let r ← opReg (σ.length - 2)
  return ([.subsReg 31 r (← opReg (σ.length - 1)), .csinc r 31 31 c], some (.i32 :: σ.drop 2))

/-- An operation on the two values on top, which the instruction `op d n m` replaces by its
result, of type `t`. -/
def genBin (ctl : List Ctl) (σ : List ValueType) (op : Fin 32 → Fin 32 → Fin 32 → Instr)
    (t : ValueType) : GenM (List Instr × Option (List ValueType)) := do
  if σ.length < curBase ctl + 2 then throw s!"an operation at height {σ.length}"
  let r ← opReg (σ.length - 2)
  return ([op r r (← opReg (σ.length - 1))], some (t :: σ.drop 2))

mutual
/-- The number of instructions of `ins` at height `h`, under constructs whose branches carry
`ar` values, the innermost first, for calls of functions whose numbers of parameters and results
`sig` gives, and the height after it, or `none` when the code after it is unreachable. -/
def instrSize (sig : Nat → Option (Nat × Nat)) (ar : List Nat) (h : Nat) :
    Instruction → Nat × Option Nat
  | .localGet _ => (1, some (h + 1))
  | .localSet _ => (1, some (h - 1))
  | .localTee _ => (1, some h)
  | .constI64 _ | .const _ => (4, some (h + 1))
  | .eqI64 | .eq | .neI64 | .ltUI64 | .leUI64 | .geUI64 => (2, some (h - 1))
  | .eqzI64 | .eqz => (2, some h)
  | .addI64 | .subI64 | .mulI64 | .andI64 | .and | .orI64 | .xorI64 | .shlI64 | .shrUI64 =>
      (1, some (h - 1))
  | .wrapI64 => (1, some h)
  | .extendUI32 => (0, some h)
  | .remUI64 => (3, some (h - 1))
  | .divUI64 => (2, some (h - 1))
  | .globalGet _ => (1, some (h + 1))
  | .globalSet _ => (1, some (h - 1))
  | .memorySize => (3, some (h + 1))
  | .memoryGrow => (16, some h)
  | .load64 _ => (6, some h)
  | .store64 _ => (6, some (h - 2))
  | .unreachable => (1, none)
  | .br n => (ar[n]?.getD 0 + 1, none)
  | .br_if n => (if ar[n]?.getD 0 = 0 then 1 else ar[n]?.getD 0 + 2, some (h - 1))
  | .ret => (ar.getLast?.getD 0 + 1, none)
  | .block _ ra body _ _ => ((listSize sig (ra :: ar) h body).1, some (h + ra))
  | .loop _ ra body _ _ => ((listSize sig (0 :: ar) h body).1, some (h + ra))
  | .iff _ ra thn els _ _ =>
      ((listSize sig (ra :: ar) (h - 1) thn).1 + (listSize sig (ra :: ar) (h - 1) els).1 + 2,
        some (h - 1 + ra))
  | .call k =>
      match sig k with
      | some (p, r) => (2 * (h - p) + p + 1 + r, some (h - p + r))
      | none => (0, none)
  | _ => (0, none)

/-- The number of instructions of `is` at height `h` and the height after them, or `none` when
their end is unreachable. -/
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
def genInstr (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt64) :
    Instruction → GenM (List Instr × Option (List ValueType))
  | .localGet i => do
      match E.localTypes[i]? with
      | some t => return ([.ldr (← opReg σ.length) 31 (← slotOf i)], some (t :: σ))
      | none => throw s!"local {i} of {E.locals}"
  | .localSet i => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ E.localTypes[i]? then
        throw s!"local.set {i} at height {σ.length}"
      return ([.str (← opReg (σ.length - 1)) 31 (← slotOf i)], some σ.tail)
  | .localTee i => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ E.localTypes[i]? then
        throw s!"local.tee {i} at height {σ.length}"
      return ([.str (← opReg (σ.length - 1)) 31 (← slotOf i)], some σ)
  | .constI64 v => do return (movImm (← opReg σ.length) v, some (.i64 :: σ))
  | .const v => do return (movImm (← opReg σ.length) v.toUInt64, some (.i32 :: σ))
  | .eqI64 | .eq => genCmp ctl σ 1
  | .neI64 => genCmp ctl σ 0
  | .ltUI64 => genCmp ctl σ 2
  | .leUI64 => genCmp ctl σ 8
  | .geUI64 => genCmp ctl σ 3
  | .addI64 => genBin ctl σ .addReg .i64
  | .subI64 => genBin ctl σ .subReg .i64
  | .mulI64 => genBin ctl σ (fun d n m => .madd d n m 31) .i64
  | .andI64 => genBin ctl σ .andReg .i64
  | .and => genBin ctl σ .andReg .i32
  | .orI64 => genBin ctl σ .orrReg .i64
  | .xorI64 => genBin ctl σ .eorReg .i64
  | .shlI64 => genBin ctl σ .lslv .i64
  | .shrUI64 => genBin ctl σ .lsrv .i64
  | .wrapI64 => do
      if σ.length < curBase ctl + 1 then throw s!"wrap at height {σ.length}"
      let r ← opReg (σ.length - 1)
      return ([.orrW r 31 r], some (.i32 :: σ.tail))
  | .eqzI64 | .eqz => do
      if σ.length < curBase ctl + 1 then throw s!"eqz at height {σ.length}"
      let r ← opReg (σ.length - 1)
      return ([.subsImm 31 r 0, .csinc r 31 31 1], some (.i32 :: σ.tail))
  | .extendUI32 => do
      if σ.length < curBase ctl + 1 then throw s!"extend at height {σ.length}"
      return ([], some (.i64 :: σ.tail))
  | .remUI64 => do
      if σ.length < curBase ctl + 2 then throw s!"a remainder at height {σ.length}"
      let x ← opReg (σ.length - 2)
      let y ← opReg (σ.length - 1)
      return ([.cbz y (← cbField a E.trapDiv), .udiv scratch x y, .msub x scratch y x],
        some (.i64 :: σ.drop 2))
  | .divUI64 => do
      if σ.length < curBase ctl + 2 then throw s!"a division at height {σ.length}"
      let x ← opReg (σ.length - 2)
      let y ← opReg (σ.length - 1)
      return ([.cbz y (← cbField a E.trapDiv), .udiv x x y], some (.i64 :: σ.drop 2))
  | .globalGet i => do
      match E.globalTypes[i]? with
      | some t =>
          if h : i + 1 < 4096 then
            return ([.ldr (← opReg σ.length) 17 ⟨i + 1, h⟩], some (t :: σ))
          else throw s!"global {i} lies beyond the area's reach"
      | none => throw s!"global {i} of {E.globalTypes.length}"
  | .globalSet i => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ E.globalTypes[i]? then
        throw s!"global.set {i} at height {σ.length}"
      if h : i + 1 < 4096 then
        return ([.str (← opReg (σ.length - 1)) 17 ⟨i + 1, h⟩], some σ.tail)
      else throw s!"global {i} lies beyond the area's reach"
  | .memorySize => do
      let d ← opReg σ.length
      return ([.ldr d 17 0, .addImm d d 8, .lsrImm d d 16], some (.i32 :: σ))
  | .memoryGrow => do
      if σ.length < curBase ctl + 1 ∨ σ.head? ≠ some .i32 then
        throw s!"memory.grow at height {σ.length}"
      if hc : E.cap < 4096 then
        let r ← opReg (σ.length - 1)
        let fail ← cbField (after a 5) (after a 12)
        let done ← bField (after a 11) (after a 16)
        return ([.ldr 16 17 0, .addImm 16 16 8, .lsrImm 16 16 16, .addReg 29 16 r,
            .subsImm 31 29 ⟨E.cap, hc⟩, .bcond 8 fail, .movz r 16 0, .lslv 29 29 r,
            .subImm 29 29 8, .str 29 17 0, mov r 16, .b done] ++ movImm r 0xFFFFFFFF, some σ)
      else throw s!"a cap of {E.cap} pages"
  | .load64 off => do
      if σ.length < curBase ctl + 1 ∨ ¬ (σ.head? = some .i32 ∨ σ.head? = some .i64) then
        throw s!"a load at height {σ.length}"
      if h : off.toNat % 8 = 0 ∧ off.toNat < 4096 then
        let r ← opReg (σ.length - 1)
        let trap ← cbField (after a 3) E.trapBounds
        return ([.ldr 16 17 0, .subImm 16 16 ⟨off.toNat, h.2⟩, .subsReg 31 r 16, .bcond 8 trap,
            .addReg 16 17 r, .ldr r 16 ⟨512 + off.toNat / 8, by omega⟩], some (.i64 :: σ.tail))
      else throw s!"a load at offset {off}"
  | .store64 off => do
      if σ.length < curBase ctl + 2 ∨ σ.head? ≠ some .i64 ∨
          ¬ (σ[1]? = some .i32 ∨ σ[1]? = some .i64) then
        throw s!"a store at height {σ.length}"
      if h : off.toNat % 8 = 0 ∧ off.toNat < 4096 then
        let v ← opReg (σ.length - 1)
        let r ← opReg (σ.length - 2)
        let trap ← cbField (after a 3) E.trapBounds
        return ([.ldr 16 17 0, .subImm 16 16 ⟨off.toNat, h.2⟩, .subsReg 31 r 16, .bcond 8 trap,
            .addReg 16 17 r, .str v 16 ⟨512 + off.toNat / 8, by omega⟩], some (σ.drop 2))
      else throw s!"a store at offset {off}"
  | .unreachable => do return ([.b (← bField a E.trapUnreachable)], none)
  | .br n => do
      match ctl[n]? with
      | some t => return (← branchTo t σ a, none)
      | none => throw s!"br {n} under {ctl.length} constructs"
  | .br_if n => do
      if σ.length < curBase ctl + 1 then throw s!"br_if at height {σ.length}"
      match ctl[n]? with
      | some t =>
          let c ← opReg (σ.length - 1)
          if t.arity = 0 then return ([.cbnz c (← cbField a t.target)], some σ.tail)
          let skip := after a (t.arity + 2)
          return (.cbz c (← cbField a skip) :: (← branchTo t σ.tail (after a 1)), some σ.tail)
      | none => throw s!"br_if {n} under {ctl.length} constructs"
  | .ret => do
      match ctl.getLast? with
      | some t => return (← branchTo t σ a, none)
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
      let (code, fin) ← genList E ({ target := a, types := [], base := σ.length } :: ctl) σ a body
      if fin.any (· ≠ rts.reverse ++ σ) then throw "a loop that ends with other types"
      return (code, some (rts.reverse ++ σ))
  | .iff pa ra thn els _ rts => do
      if pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra ∨ σ.length < curBase ctl + 1 then
        throw "an if with parameters, more than one result, results without types, or no condition"
      let c ← opReg (σ.length - 1)
      let ar := ra :: ctl.map (·.arity)
      let aB := after a (1 + (listSize (sigOf E.callee) ar (σ.length - 1) thn).1)
      let aElse := after aB 1
      let aEnd := after aElse (listSize (sigOf E.callee) ar (σ.length - 1) els).1
      let inner := { target := aEnd, types := rts.reverse, base := σ.length - 1 } :: ctl
      let (ti, ta) ← genList E inner σ.tail (after a 1) thn
      let (ei, ea) ← genList E inner σ.tail aElse els
      if ta.any (· ≠ rts.reverse ++ σ.tail) ∨ ea.any (· ≠ rts.reverse ++ σ.tail) then
        throw "an if whose branches end with other types"
      return ([.cbz c (← cbField a aElse)] ++ ti ++ [.b (← bField aB aEnd)] ++ ei,
        some (rts.reverse ++ σ.tail))
  | .call k => do
      match E.callee k with
      | none => throw s!"a call of function {k}, which the program lacks"
      | some (target, ps, rs) =>
          if hc : σ.length < curBase ctl + ps.length ∨ 26 < σ.length ∨
              26 < σ.length - ps.length + rs.length ∨
              4096 ≤ E.locals + spillSlots ∨ σ.take ps.length ≠ ps.reverse then
            throw s!"a call of function {k} at height {σ.length}"
          else
            have hs : spillSlots = 26 := rfl
            let spills := List.ofFn fun j : Fin (σ.length - ps.length) =>
              Instr.str (regOf j) 31 ⟨E.locals + j, by omega⟩
            let moves := List.ofFn fun i : Fin ps.length =>
              mov (regOf i) (regOf (σ.length - ps.length + i))
            let res := List.ofFn fun k : Fin rs.length =>
              mov (regOf (σ.length - ps.length + (rs.length - 1 - k))) (regOf (rs.length - 1 - k))
            let reloads := List.ofFn fun j : Fin (σ.length - ps.length) =>
              Instr.ldr (regOf j) 31 ⟨E.locals + j, by omega⟩
            let call := Instr.bl (← bField (after a (σ.length - ps.length + ps.length)) target)
            return (spills ++ moves ++ [call] ++ res ++ reloads,
              some (rs.reverse ++ σ.drop ps.length))
  | i => throw s!"the form {repr i} lies outside the generator's forms"

/-- The instructions of `is` placed at `a`, on the operand stack of types `σ` under the
constructs `ctl`, and the types after them, or `none` when their end is unreachable. -/
def genList (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt64) :
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

/-- A numeric value type, whose zero is the word 0. -/
def numeric : ValueType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | _ => false

/-- The frame of a function with `n` parameters and locals: 8 bytes for each, 8 for each spill
slot above them, and 8 for the return address above those, rounded up to 16. -/
def frameSize (n : Nat) : Nat := (8 * (n + spillSlots + 1) + 15) / 16 * 16

/-- The number of instructions of the function `f`, whose calls name functions whose numbers of
parameters and results `sig` gives. -/
def functionSize (sig : Nat → Option (Nat × Nat)) (f : Function) : Nat :=
  5 + (f.params.length + f.locals.length) + (listSize sig [f.results.length] 0 f.body).1 + 3

/-- The instructions of the function `f` placed at `entry`.  The prologue sets X16 to SP less
the frame's size, compares it with the stack's limit in X18, and branches to `trapStack` when it
lies below; it then allocates the frame, saves the return address in X30 above the spill slots,
and stores the parameters from X0 up and zeros for the other locals.  The body follows, then the
epilogue, which restores X30, frees the frame, and returns.  Its calls name the functions of
`callee`. -/
def genFunction (callee : Table) (S : Shared) (entry : UInt64) (f : Function) :
    GenM (List Instr) := do
  let p := f.params.length
  let n := p + f.locals.length
  let r := f.results.length
  if p > 26 ∨ r > 26 then throw "a function with more than 26 parameters or 26 results"
  if !f.locals.all numeric then throw "a local whose zero is not the word 0"
  if hf : frameSize n < 4096 then
    have hn : n + spillSlots < 4096 := by unfold frameSize at hf; omega
    let bodyA := after entry (5 + n)
    let E : Env := { toShared := S, localTypes := f.params ++ f.locals, callee }
    let epilogue := after bodyA (listSize (sigOf callee) [r] 0 f.body).1
    let (body, fin) ←
      genList E [{ target := epilogue, types := f.results.reverse, base := 0 }] [] bodyA f.body
    if fin.any (· ≠ f.results.reverse) then throw "a function body that ends with other types"
    let stores := List.ofFn fun i : Fin n =>
      Instr.str (if i.val < p then regOf i.val else 31) 31 ⟨i.val, by omega⟩
    let check := Instr.bcond 3 (← cbField (after entry 2) S.trapStack)
    return [.subImm 16 31 ⟨frameSize n, hf⟩, .subsReg 31 16 18, check,
        .subImm 31 31 ⟨frameSize n, hf⟩, .str 30 31 ⟨n + spillSlots, hn⟩] ++ stores ++ body ++
      [.ldr 30 31 ⟨n + spillSlots, hn⟩, .addImm 31 31 ⟨frameSize n, hf⟩, .ret 30]
  else throw s!"a frame of {frameSize n} bytes"

/-- What `main` writes to the UART from the result: the eight bytes of its word, or the array of
words in the memory at the pointer that it is, its length word and then its elements. -/
inductive Output where
  | word
  | array
deriving DecidableEq

/-- The writes of the eight bytes of register `r` to the UART at X1 through X2, the lowest first. -/
def writesOf (r : Fin 32) : List Instr :=
  (List.range 8).flatMap fun i =>
    [Instr.lsrImm 2 r ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]

/-- The number of instructions of `main`'s output of the kind `o`. -/
def outSize : Output → Nat
  | .word => 16
  | .array => 39

/-- `main`'s output of the result in X0, placed at `a`.  For an array, X3 holds the address of a
word of the array in the area, X4 the number of elements that remain, and X6 the element. -/
def genOut (a : UInt64) : Output → GenM (List Instr)
  | .word => pure (writesOf 0)
  | .array => do
      let cz ← cbField (after a 18) (after a 39)
      let back ← bField (after a 38) (after a 18)
      return [.addReg 3 17 0, .ldr 4 3 512] ++ writesOf 4 ++ [.cbz 4 cz, .addImm 3 3 8,
        .ldr 6 3 512] ++ writesOf 6 ++ [.subImm 4 4 1, .b back]

/-- The number of instructions of `main` for `k` arguments and the output `o`. -/
def mainSize (k : Nat) (o : Output) : Nat := 3 + 4 + 1 + 4 + 4 * k + 1 + 4 + outSize o + 4 + 3

/-- `main` placed at `a`: it saves X30, sets the stack's limit in X18 to `room` bytes below its
SP and X17 to the area at `area`, calls the function at `entry` with `args`, writes the result to
the UART at `uart` as `o` says, and returns 0. -/
def genMain (a entry : UInt64) (args : List UInt64) (uart room area : UInt64) (o : Output) :
    GenM (List Instr) := do
  if args.length > 8 then throw "more than 8 arguments"
  let loads := args.zipIdx.flatMap fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v
  let call := Instr.bl (← bField (after a (12 + 4 * args.length)) entry)
  let out ← genOut (after a (17 + 4 * args.length)) o
  return [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
    [.subReg 18 18 16] ++ movImm 17 area ++ loads ++ [call] ++ movImm 1 uart ++ out ++
    movImm 0 0 ++ [.ldr 30 31 0, .addImm 31 31 16, .ret 30]

mutual
/-- The indices of the functions that `ins` calls. -/
def callsOf : Instruction → List Nat
  | .call k => [k]
  | .block _ _ body _ _ => callsIn body
  | .loop _ _ body _ _ => callsIn body
  | .iff _ _ thn els _ _ => callsIn thn ++ callsIn els
  | _ => []

/-- The indices of the functions that the instructions `is` call. -/
def callsIn : List Instruction → List Nat
  | [] => []
  | i :: rest => callsOf i ++ callsIn rest
end

/-- The functions of `m` that calls reach from those of `todo`, after those of `done`, each
once, within `fuel` steps. -/
def reachable (m : Module) : Nat → List Nat → List Nat → List Nat
  | 0, done, _ => done
  | _ + 1, done, [] => done
  | fuel + 1, done, j :: todo =>
      if j ∈ done then reachable m fuel done todo
      else reachable m fuel (done ++ [j])
        (todo ++ ((m.funcs[j]?).map fun f => callsIn f.body).getD [])

/-- The functions that calls reach from function `k` of `m`, `k` first. -/
def reachFrom (m : Module) (k : Nat) : List Nat :=
  reachable m (1 + (m.funcs.map fun f => (callsIn f.body).length).sum) [] [k]

/-- The functions that the calls of the functions that calls reach from function `k` of `m`
name. -/
def callTargets (m : Module) (k : Nat) : List Nat :=
  (reachFrom m k).flatMap fun j => ((m.funcs[j]?).map fun f => callsIn f.body).getD []

/-- Function `j` of `m` with its index. -/
def funcOf (m : Module) (j : Nat) : GenM (Nat × Function) :=
  match m.funcs[j]? with
  | some f => pure (j, f)
  | none => throw s!"no function {j}"

/-- The numbers of parameters and results of the functions of `fs` that `targets` names, by
index. -/
def sigIn (targets : List Nat) (fs : List (Nat × Function)) (k : Nat) : Option (Nat × Nat) :=
  if k ∈ targets then
    (fs.find? (·.1 = k)).map fun (_, f) => (f.params.length, f.results.length)
  else none

/-- The entries of the functions of `fs`, laid out one after another from `a`, with the types of
their parameters and results, by index. -/
def entriesFrom (sig : Nat → Option (Nat × Nat)) :
    UInt64 → List (Nat × Function) → List (Nat × UInt64 × List ValueType × List ValueType)
  | _, [] => []
  | a, (j, f) :: rest =>
      (j, a, f.params, f.results) :: entriesFrom sig (after a (functionSize sig f)) rest

/-- The address after the functions of `fs`, laid out one after another from `a`. -/
def endOf (sig : Nat → Option (Nat × Nat)) : UInt64 → List (Nat × Function) → UInt64
  | a, [] => a
  | a, (_, f) :: rest => endOf sig (after a (functionSize sig f)) rest

/-- The instructions of the functions of `fs`, one after another from `a`. -/
def genFunctions (callee : Table) (S : Shared) :
    UInt64 → List (Nat × Function) → GenM (List Instr)
  | _, [] => pure []
  | a, (_, f) :: rest => do
      let is ← genFunction callee S a f
      return is ++ (← genFunctions callee S (after a is.length) rest)

/-- The entry of function `j` and the types of its parameters and results, among the functions
of `fs` laid out one after another from `a`. -/
def entryIn (sig : Nat → Option (Nat × Nat)) (a : UInt64) (fs : List (Nat × Function))
    (j : Nat) : Option (UInt64 × List ValueType × List ValueType) :=
  ((entriesFrom sig a fs).find? (·.1 = j)).map (·.2)

/-- The table of the calls of the functions of `fs`, laid out one after another from `a`: the
functions that `targets` names. -/
def tableOf (targets : List Nat) (a : UInt64) (fs : List (Nat × Function)) : Table :=
  fun j => if j ∈ targets then entryIn (sigIn targets fs) a fs j else none

/-- The type of a number. -/
def valueType : Value → Option ValueType
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .f32 _ => some .f32
  | .f64 _ => some .f64
  | _ => none

/-- The types of the globals of `m`, when each is a number. -/
def globalTypesOf (m : Module) : Option (List ValueType) :=
  m.globals.mapM fun g => valueType g.init

/-- The memory of `m` fits an area of `cap` pages: it has 32-bit addresses and between 1 and
`cap` pages, and `cap` lies below 4096. -/
def areaOk (m : Module) (cap : Nat) : Bool :=
  match m.memory with
  | some d => !d.is64 && 1 ≤ d.pagesMin.toNat && d.pagesMin.toNat ≤ cap && cap < 4096
  | none => false

/-- The number of bytes of the area of a memory of `cap` pages. -/
def areaSize (cap : Nat) : Nat := 4096 + cap * 65536

/-- Byte `k` of the word `w`, the lowest first. -/
def byteOf (w : UInt64) (k : Nat) : UInt8 := (w >>> UInt64.ofNat (8 * k)).toUInt8

/-- The word of a number in a register. -/
def wordOf : Value → UInt64
  | .i32 x => x.toUInt64
  | .i64 x => x
  | .f32 x => x.toUInt64
  | .f64 x => x
  | _ => 0

/-- Byte `j` of the area of the store `st`: the size of its memory less 8, the words of its
globals from byte 8, and from byte 4096 the bytes of its memory. -/
def areaByte (st : Store Unit) (j : Nat) : UInt8 :=
  if j < 8 then byteOf (UInt64.ofNat (st.mem.pages * 65536 - 8)) j
  else if j < 4096 then
    match st.globals.globals[j / 8 - 1]? with
    | some v => byteOf (wordOf v) (j % 8)
    | none => 0
  else st.mem.bytes (j - 4096)

/-- The bytes of the area of module `m` with `cap` pages, as the module starts. -/
def areaBytes (m : Module) (cap : Nat) : List UInt8 :=
  (List.range (areaSize cap)).map (areaByte m.initialStore)

/-- The program that runs function `k` of `m` on `args`, placed after its exit word at `base`,
with a stack of `room` bytes below `main`'s frame and the module's store in an area at `area` with
a memory of `cap` pages: `main` at `base + 4`, the functions that calls reach from function `k`,
`k` first, and the trap stubs of codes 1, 2, 3, and 4, each `movImm` of X0 and a branch to the
exit word.  The parameters of function `k` are `i64`s, the memory satisfies `areaOk`, and the
globals are at most 511 numbers.  The table of the functions' calls holds the functions that
`callTargets` names.  `main` writes the result as `o` says.  The image puts a branch to `lx_exit`
at `base` and `areaBytes` at `area`. -/
def genProgram (m : Module) (k : Nat) (args : List UInt64) (uart base room area : UInt64)
    (cap : Nat) (o : Output) : GenM (List Instr) := do
  if !areaOk m cap then throw s!"a memory that an area of {cap} pages does not hold"
  let gts ← match globalTypesOf m with
    | some gts => if gts.length ≤ 511 then pure gts else throw "more than 511 globals"
    | none => throw "a global that is not a number"
  let fs ← (reachFrom m k).mapM (funcOf m)
  let targets := callTargets m k
  let sig := sigIn targets fs
  let mainA := after base 1
  let first := after mainA (mainSize args.length o)
  let callee := tableOf targets first fs
  let traps := endOf sig first fs
  let entry ← match entryIn sig first fs k with
    | some (e, ps, _) =>
        if ps.all (· == .i64) then pure e else throw s!"function {k} takes a value of another type"
    | none => throw s!"no function {k}"
  let main ← genMain mainA entry args uart room area o
  let S : Shared :=
    { trapUnreachable := traps, trapBounds := after traps 5, trapDiv := after traps 10,
      trapStack := after traps 15, cap, globalTypes := gts }
  let fns ← genFunctions callee S first fs
  let stub (a : UInt64) (code : Nat) : GenM (List Instr) := do
    return movImm 0 (UInt64.ofNat code) ++ [.b (← bField (after a 4) base)]
  return main ++ fns ++ (← stub traps 1) ++ (← stub (after traps 5) 2) ++
    (← stub (after traps 10) 3) ++ (← stub (after traps 15) 4)

end LeanExe.A64
