import Interpreter.Wasm.Syntax
import LeanExe.A64.Encode

/-!
The code generator of the AArch64 back end: from a function of a module of the verified
compiler and its arguments, a bare-metal program of the model's instruction forms whose `main`
calls the function, writes the eight bytes of its result to the UART, and returns 0 to the
startup code of `tools/baremetal/start.S`.  It covers the Wasm forms of GCD's loop and the
integer comparisons and operations of the C path's subset, and it rejects every other form with a
message.

The operand stack's height and types are fixed at every reachable instruction, so the value at
height `h` lies in the register `opReg h`, X0 to X15 and then X19 to X28.  An `i32` lies there
zero-extended, so `extendUI32` emits nothing, `wrapI64` is a 32-bit `ORR`, and an `i32` comparison
or `and` is the 64-bit one.  X16 is the scratch register of `remUI64` and of the prologue.  A
function keeps its parameters and locals in a frame at `SP` of 8 bytes each, followed by 26 spill
slots and the slot of the return address, a multiple of 16 bytes in all.  Its prologue checks that
the frame fits above the stack's limit, which X18 holds, reserves the frame, stores the parameters
into it from X0 upward, and clears the other locals.  A call spills the operand registers below its
arguments to the spill slots, moves the arguments into X0 upward, branches with `BL`, moves the
result from X0 into the register of its height, and reloads the spilled registers.  The callee may
change every register but SP and X18, and it changes no memory from its caller's SP upward.  A
construct carries at most one value, and a branch to one moves the value that it carries, if any,
into the register of the construct's base height with one `ORR` and branches to the construct's
target: the end of a `block` or an `iff`, the start of a `loop`, or the epilogue for the function
itself, which also serves `ret`.  The result lies at height 0, in X0, when the epilogue releases the
frame and returns.  Code after a `br`, a `ret`, or `unreachable` in the same list is unreachable,
and the generator emits nothing for it, while the code after a construct is reachable, as Wasm's
typing has it.  No instruction may pop below the base height of its innermost construct, `curBase`,
as valid Wasm never does: Talos runs a construct's body on the whole operand stack and restores the
values below the construct afterwards, which the registers of those heights would not follow.  A
trap branches to a stub that sets X0 to the trap's code of `LeanExe.Native.trapCode`, 1, 2, or 3, or
to 4 for an overflow of the stack, and branches to the program's exit word, which the image fills
with a branch to `lx_exit` of the startup code.

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

/-- A construct that a branch can target: the target's address, the number of values that a
branch to it carries, and the height under those values at the target. -/
structure Ctl where
  target : UInt64
  arity : Nat
  base : Nat

/-- What the instructions of one function need: the number of its locals, parameters
included, the addresses of the trap stubs for `unreachable`, for a division by zero, and for a
stack that a frame would overflow, and for each function that a call may name, its entry, its
number of parameters, and its number of results. -/
structure Env where
  locals : Nat
  trapUnreachable : UInt64
  trapDiv : UInt64
  trapStack : UInt64
  callee : Nat → Option (UInt64 × Nat × Nat)

/-- The numbers of parameters and results of the functions of the table `callee`. -/
def sigOf (callee : Nat → Option (UInt64 × Nat × Nat)) (k : Nat) : Option (Nat × Nat) :=
  (callee k).map fun c => (c.2.1, c.2.2)

/-- The height of the innermost construct's base, under which its code must not pop. -/
def curBase : List Ctl → Nat
  | [] => 0
  | t :: _ => t.base

/-- The move of a branch from height `h` to `t`, placed at `a`, when the branch carries a value,
and the branch.  A construct carries at most one value, as the subset of
`LeanExe/Native/Subset.lean` requires. -/
def branchTo (t : Ctl) (h : Nat) (a : UInt64) : GenM (List Instr) := do
  if h < t.base + t.arity ∨ t.arity > 1 then
    throw "a branch with fewer values than its target takes, or with more than one"
  let moves ← if t.arity = 1 then do pure [mov (← opReg t.base) (← opReg (h - 1))]
    else pure []
  return moves ++ [.b (← bField (after a t.arity) t.target)]

/-- A comparison of the two values on top, which `SUBS` and `CSINC` with the condition `c`, the
inverse of the comparison's, replace by 1 or 0. -/
def genCmp (ctl : List Ctl) (h : Nat) (c : Fin 16) : GenM (List Instr × Option Nat) := do
  if h < curBase ctl + 2 then throw s!"a comparison at height {h}"
  let r ← opReg (h - 2)
  return ([.subsReg 31 r (← opReg (h - 1)), .csinc r 31 31 c], some (h - 1))

/-- An operation on the two values on top, which the instruction `op d n m` replaces by its
result. -/
def genBin (ctl : List Ctl) (h : Nat) (op : Fin 32 → Fin 32 → Fin 32 → Instr) :
    GenM (List Instr × Option Nat) := do
  if h < curBase ctl + 2 then throw s!"an operation at height {h}"
  let r ← opReg (h - 2)
  return ([op r r (← opReg (h - 1))], some (h - 1))

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
/-- The instructions of `ins` placed at `a`, at height `h` under the constructs `ctl`, and the
height after it, or `none` when the code after it is unreachable. -/
def genInstr (E : Env) (ctl : List Ctl) (h : Nat) (a : UInt64) :
    Instruction → GenM (List Instr × Option Nat)
  | .localGet i => do
      if i ≥ E.locals then throw s!"local {i} of {E.locals}"
      return ([.ldr (← opReg h) 31 (← slotOf i)], some (h + 1))
  | .localSet i => do
      if i ≥ E.locals ∨ h < curBase ctl + 1 then throw s!"local.set {i} at height {h}"
      return ([.str (← opReg (h - 1)) 31 (← slotOf i)], some (h - 1))
  | .localTee i => do
      if i ≥ E.locals ∨ h < curBase ctl + 1 then throw s!"local.tee {i} at height {h}"
      return ([.str (← opReg (h - 1)) 31 (← slotOf i)], some h)
  | .constI64 v => do return (movImm (← opReg h) v, some (h + 1))
  | .const v => do return (movImm (← opReg h) v.toUInt64, some (h + 1))
  | .eqI64 | .eq => genCmp ctl h 1
  | .neI64 => genCmp ctl h 0
  | .ltUI64 => genCmp ctl h 2
  | .leUI64 => genCmp ctl h 8
  | .geUI64 => genCmp ctl h 3
  | .addI64 => genBin ctl h .addReg
  | .subI64 => genBin ctl h .subReg
  | .mulI64 => genBin ctl h fun d n m => .madd d n m 31
  | .andI64 | .and => genBin ctl h .andReg
  | .orI64 => genBin ctl h .orrReg
  | .xorI64 => genBin ctl h .eorReg
  | .shlI64 => genBin ctl h .lslv
  | .shrUI64 => genBin ctl h .lsrv
  | .wrapI64 => do
      if h < curBase ctl + 1 then throw s!"wrap at height {h}"
      let r ← opReg (h - 1)
      return ([.orrW r 31 r], some h)
  | .eqzI64 | .eqz => do
      if h < curBase ctl + 1 then throw s!"eqz at height {h}"
      let r ← opReg (h - 1)
      return ([.subsImm 31 r 0, .csinc r 31 31 1], some h)
  | .extendUI32 => do
      if h < curBase ctl + 1 then throw s!"extend at height {h}"
      return ([], some h)
  | .remUI64 => do
      if h < curBase ctl + 2 then throw s!"a remainder at height {h}"
      let x ← opReg (h - 2)
      let y ← opReg (h - 1)
      return ([.cbz y (← cbField a E.trapDiv), .udiv scratch x y, .msub x scratch y x],
        some (h - 1))
  | .divUI64 => do
      if h < curBase ctl + 2 then throw s!"a division at height {h}"
      let x ← opReg (h - 2)
      let y ← opReg (h - 1)
      return ([.cbz y (← cbField a E.trapDiv), .udiv x x y], some (h - 1))
  | .unreachable => do return ([.b (← bField a E.trapUnreachable)], none)
  | .br n => do
      match ctl[n]? with
      | some t => return (← branchTo t h a, none)
      | none => throw s!"br {n} under {ctl.length} constructs"
  | .br_if n => do
      if h < curBase ctl + 1 then throw s!"br_if at height {h}"
      match ctl[n]? with
      | some t =>
          let c ← opReg (h - 1)
          if t.arity = 0 then return ([.cbnz c (← cbField a t.target)], some (h - 1))
          let skip := after a (t.arity + 2)
          return (.cbz c (← cbField a skip) :: (← branchTo t (h - 1) (after a 1)), some (h - 1))
      | none => throw s!"br_if {n} under {ctl.length} constructs"
  | .ret => do
      match ctl.getLast? with
      | some t => return (← branchTo t h a, none)
      | none => throw "ret outside a function"
  | .block pa ra body _ _ => do
      if pa ≠ 0 ∨ ra > 1 then throw "a block with parameters or more than one result"
      let n := (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) h body).1
      let inner := { target := after a n, arity := ra, base := h } :: ctl
      let (code, fin) ← genList E inner h a body
      if fin.any (· ≠ h + ra) then throw "a block that ends at another height"
      return (code, some (h + ra))
  | .loop pa ra body _ _ => do
      if pa ≠ 0 ∨ ra > 1 then throw "a loop with parameters or more than one result"
      let (code, fin) ← genList E ({ target := a, arity := 0, base := h } :: ctl) h a body
      if fin.any (· ≠ h + ra) then throw "a loop that ends at another height"
      return (code, some (h + ra))
  | .iff pa ra thn els _ _ => do
      if pa ≠ 0 ∨ ra > 1 ∨ h < curBase ctl + 1 then
        throw "an if with parameters, more than one result, or no condition"
      let c ← opReg (h - 1)
      let ar := ra :: ctl.map (·.arity)
      let aB := after a (1 + (listSize (sigOf E.callee) ar (h - 1) thn).1)
      let aElse := after aB 1
      let aEnd := after aElse (listSize (sigOf E.callee) ar (h - 1) els).1
      let inner := { target := aEnd, arity := ra, base := h - 1 } :: ctl
      let (ti, ta) ← genList E inner (h - 1) (after a 1) thn
      let (ei, ea) ← genList E inner (h - 1) aElse els
      if ta.any (· ≠ h - 1 + ra) ∨ ea.any (· ≠ h - 1 + ra) then
        throw "an if whose branches end at another height"
      return ([.cbz c (← cbField a aElse)] ++ ti ++ [.b (← bField aB aEnd)] ++ ei,
        some (h - 1 + ra))
  | .call k => do
      match E.callee k with
      | none => throw s!"a call of function {k}, which the program lacks"
      | some (target, p, r) =>
          if hc : h < curBase ctl + p ∨ 26 < h ∨ 26 < h - p + r ∨ 1 < r ∨ 8 < p ∨
              4096 ≤ E.locals + spillSlots then
            throw s!"a call of function {k} at height {h}"
          else
            have hs : spillSlots = 26 := rfl
            let spills := List.ofFn fun j : Fin (h - p) =>
              Instr.str (regOf j) 31 ⟨E.locals + j, by omega⟩
            let moves := List.ofFn fun i : Fin p => mov ⟨i, by omega⟩ (regOf (h - p + i))
            let res := if r = 1 then [mov (regOf (h - p)) 0] else []
            let reloads := List.ofFn fun j : Fin (h - p) =>
              Instr.ldr (regOf j) 31 ⟨E.locals + j, by omega⟩
            let call := Instr.bl (← bField (after a (h - p + p)) target)
            return (spills ++ moves ++ [call] ++ res ++ reloads, some (h - p + r))
  | i => throw s!"the form {repr i} lies outside the generator's forms"

/-- The instructions of `is` placed at `a`, at height `h` under the constructs `ctl`, and the
height after them, or `none` when their end is unreachable. -/
def genList (E : Env) (ctl : List Ctl) (h : Nat) (a : UInt64) :
    List Instruction → GenM (List Instr × Option Nat)
  | [] => return ([], some h)
  | i :: rest => do
      let (c1, fin) ← genInstr E ctl h a i
      match fin with
      | none => return (c1, none)
      | some h' =>
          let (c2, fin') ← genList E ctl h' (after a c1.length) rest
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
def genFunction (callee : Nat → Option (UInt64 × Nat × Nat))
    (trapUnreachable trapDiv trapStack entry : UInt64) (f : Function) : GenM (List Instr) := do
  let p := f.params.length
  let n := p + f.locals.length
  let r := f.results.length
  if p > 8 ∨ r > 1 then throw "a function with more than 8 parameters or 1 result"
  if !f.locals.all numeric then throw "a local whose zero is not the word 0"
  if hf : frameSize n < 4096 then
    have hn : n + spillSlots < 4096 := by unfold frameSize at hf; omega
    let bodyA := after entry (5 + n)
    let E : Env := { locals := n, trapUnreachable, trapDiv, trapStack, callee }
    let epilogue := after bodyA (listSize (sigOf callee) [r] 0 f.body).1
    let (body, fin) ← genList E [{ target := epilogue, arity := r, base := 0 }] 0 bodyA f.body
    if fin.any (· ≠ r) then throw "a function body that ends at another height"
    let stores := List.ofFn fun i : Fin n =>
      Instr.str (if i.val < p then ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩ else 31) 31
        ⟨i.val, by omega⟩
    let check := Instr.bcond 3 (← cbField (after entry 2) trapStack)
    return [.subImm 16 31 ⟨frameSize n, hf⟩, .subsReg 31 16 18, check,
        .subImm 31 31 ⟨frameSize n, hf⟩, .str 30 31 ⟨n + spillSlots, hn⟩] ++ stores ++ body ++
      [.ldr 30 31 ⟨n + spillSlots, hn⟩, .addImm 31 31 ⟨frameSize n, hf⟩, .ret 30]
  else throw s!"a frame of {frameSize n} bytes"

/-- The number of instructions of `main` for `k` arguments. -/
def mainSize (k : Nat) : Nat := 3 + 4 + 1 + 4 * k + 1 + 4 + 16 + 4 + 3

/-- `main` placed at `a`: it saves X30, sets the stack's limit in X18 to `room` bytes below its
SP, calls the function at `entry` with `args`, writes the eight bytes of the result to the UART
at `uart`, the lowest first, and returns 0. -/
def genMain (a entry : UInt64) (args : List UInt64) (uart room : UInt64) :
    GenM (List Instr) := do
  if args.length > 8 then throw "more than 8 arguments"
  let loads := args.zipIdx.flatMap fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v
  let writes := (List.range 8).flatMap fun i =>
    [Instr.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]
  let call := Instr.bl (← bField (after a (8 + 4 * args.length)) entry)
  return [.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
    [.subReg 18 18 16] ++ loads ++ [call] ++ movImm 1 uart ++ writes ++ movImm 0 0 ++
    [.ldr 30 31 0, .addImm 31 31 16, .ret 30]

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

/-- The entries of the functions of `fs`, laid out one after another from `a`, with their
numbers of parameters and results, by index. -/
def entriesFrom (sig : Nat → Option (Nat × Nat)) :
    UInt64 → List (Nat × Function) → List (Nat × UInt64 × Nat × Nat)
  | _, [] => []
  | a, (j, f) :: rest =>
      (j, a, f.params.length, f.results.length) ::
        entriesFrom sig (after a (functionSize sig f)) rest

/-- The address after the functions of `fs`, laid out one after another from `a`. -/
def endOf (sig : Nat → Option (Nat × Nat)) : UInt64 → List (Nat × Function) → UInt64
  | a, [] => a
  | a, (_, f) :: rest => endOf sig (after a (functionSize sig f)) rest

/-- The instructions of the functions of `fs`, one after another from `a`. -/
def genFunctions (callee : Nat → Option (UInt64 × Nat × Nat)) (tU tD tS : UInt64) :
    UInt64 → List (Nat × Function) → GenM (List Instr)
  | _, [] => pure []
  | a, (_, f) :: rest => do
      let is ← genFunction callee tU tD tS a f
      return is ++ (← genFunctions callee tU tD tS (after a is.length) rest)

/-- The entry of function `j` and its numbers of parameters and results, among the functions of
`fs` laid out one after another from `a`. -/
def entryIn (sig : Nat → Option (Nat × Nat)) (a : UInt64) (fs : List (Nat × Function))
    (j : Nat) : Option (UInt64 × Nat × Nat) :=
  ((entriesFrom sig a fs).find? (·.1 = j)).map (·.2)

/-- The table of the calls of the functions of `fs`, laid out one after another from `a`: the
functions that `targets` names. -/
def tableOf (targets : List Nat) (a : UInt64) (fs : List (Nat × Function)) :
    Nat → Option (UInt64 × Nat × Nat) :=
  fun j => if j ∈ targets then entryIn (sigIn targets fs) a fs j else none

/-- The program that runs function `k` of `m` on `args`, placed after its exit word at `base`,
with a stack of `room` bytes below `main`'s frame: `main` at `base + 4`, the functions that calls
reach from function `k`, `k` first, and the trap stubs of codes 1, 2, 3, and 4, each `movImm` of
X0 and a branch to the exit word.  The table of the functions' calls holds the functions that
`callTargets` names.  The image puts a branch to `lx_exit` at `base`. -/
def genProgram (m : Module) (k : Nat) (args : List UInt64) (uart base room : UInt64) :
    GenM (List Instr) := do
  let fs ← (reachFrom m k).mapM (funcOf m)
  let targets := callTargets m k
  let sig := sigIn targets fs
  let mainA := after base 1
  let first := after mainA (mainSize args.length)
  let callee := tableOf targets first fs
  let traps := endOf sig first fs
  let entry ← match entryIn sig first fs k with
    | some (e, _, _) => pure e
    | none => throw s!"no function {k}"
  let main ← genMain mainA entry args uart room
  let fns ← genFunctions callee traps (after traps 10) (after traps 15) first fs
  let stub (a : UInt64) (code : Nat) : GenM (List Instr) := do
    return movImm 0 (UInt64.ofNat code) ++ [.b (← bField (after a 4) base)]
  return main ++ fns ++ (← stub traps 1) ++ (← stub (after traps 5) 2) ++
    (← stub (after traps 10) 3) ++ (← stub (after traps 15) 4)

end LeanExe.A64
