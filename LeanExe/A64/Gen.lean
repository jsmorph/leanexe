import Interpreter.Wasm.Syntax
import LeanExe.A64.Encode

/-!
The code generator of the AArch64 back end: from a function of a module of the verified
compiler and its arguments, a bare-metal program of the model's instruction forms whose `main`
calls the function, writes the eight bytes of its result to the UART, and returns 0 to the
startup code of `tools/baremetal/start.S`.  This increment covers the Wasm forms of GCD's loop
and rejects every other form with a message.

The operand stack's height and types are fixed at every reachable instruction, so the value at
height `h` lies in the register `opReg h`, X0 to X15 and then X19 to X28.  An `i32` lies there
zero-extended, so `extendUI32` emits nothing.  X16 is the scratch register of `remUI64`.  A
function keeps its parameters and locals in a frame of 8 bytes each at `SP`, which its prologue
reserves, a multiple of 16 bytes, stores its parameters into from X0 upward, and clears for the
other locals.  A branch to a construct moves the values that the branch carries into the
registers of the construct's base height, one `ORR` each, and branches to the construct's target:
the end of a `block` or an `iff`, the start of a `loop`, or the epilogue for the function itself,
which also serves `ret`.  The result lies at height 0, in X0, when the epilogue releases the frame
and returns.  Code after a `br`, a `ret`, or `unreachable` in the same list is unreachable, and the
generator emits nothing for it, while the code after a construct is reachable, as Wasm's typing
has it.  No instruction may pop below the base height of its innermost construct, `curBase`, as
valid Wasm never does: Talos runs a construct's body on the whole operand stack and restores the
values below the construct afterwards, which the registers of those heights would not follow.
A trap branches to a stub that sets X0 to the trap's code of `LeanExe.Native.trapCode`, 1, 2, or
3, and branches to the program's exit word, which the image fills with a branch to `lx_exit` of
the startup code.

The generator places code as it emits it: each function takes the address of its first
instruction, and `instrSize` and `listSize` give the number of instructions of a construct
without addresses, so a construct's end is known before its body is emitted.  Every branch is
encoded with its offset after a check that the offset fits.
-/

namespace LeanExe.A64

open Wasm

/-- The registers of the operand stack's heights. -/
def opRegs : List Nat := List.range 16 ++ (List.range 10).map (· + 19)

/-- The scratch register. -/
def scratch : Fin 32 := 16

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
included, and the addresses of the trap stubs for `unreachable` and for a division by zero. -/
structure Env where
  locals : Nat
  trapUnreachable : UInt64
  trapDiv : UInt64

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

mutual
/-- The number of instructions of `ins` under constructs whose branches carry `ar` values, the
innermost first, and whether the code after it is reachable. -/
def instrSize (ar : List Nat) : Instruction → Nat × Bool
  | .localGet _ | .localSet _ | .localTee _ => (1, true)
  | .constI64 _ | .const _ => (4, true)
  | .eqI64 | .eq | .eqzI64 | .eqz => (2, true)
  | .extendUI32 => (0, true)
  | .remUI64 => (3, true)
  | .divUI64 => (2, true)
  | .unreachable => (1, false)
  | .br n => (ar[n]?.getD 0 + 1, false)
  | .br_if n => (if ar[n]?.getD 0 = 0 then 1 else ar[n]?.getD 0 + 2, true)
  | .ret => (ar.getLast?.getD 0 + 1, false)
  | .block _ ra body _ _ => ((listSize (ra :: ar) body).1, true)
  | .loop _ _ body _ _ => ((listSize (0 :: ar) body).1, true)
  | .iff _ ra thn els _ _ =>
      ((listSize (ra :: ar) thn).1 + (listSize (ra :: ar) els).1 + 2, true)
  | _ => (0, true)

/-- The number of instructions of `is` and whether the code after them is reachable. -/
def listSize (ar : List Nat) : List Instruction → Nat × Bool
  | [] => (0, true)
  | i :: rest =>
      if (instrSize ar i).2 then
        ((instrSize ar i).1 + (listSize ar rest).1, (listSize ar rest).2)
      else ((instrSize ar i).1, false)
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
  | .eqI64 | .eq => do
      if h < curBase ctl + 2 then throw s!"a comparison at height {h}"
      let r ← opReg (h - 2)
      return ([.subsReg 31 r (← opReg (h - 1)), .csinc r 31 31 1], some (h - 1))
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
      let n := (listSize (ra :: ctl.map (·.arity)) body).1
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
      let aB := after a (1 + (listSize ar thn).1)
      let aElse := after aB 1
      let aEnd := after aElse (listSize ar els).1
      let inner := { target := aEnd, arity := ra, base := h - 1 } :: ctl
      let (ti, ta) ← genList E inner (h - 1) (after a 1) thn
      let (ei, ea) ← genList E inner (h - 1) aElse els
      if ta.any (· ≠ h - 1 + ra) ∨ ea.any (· ≠ h - 1 + ra) then
        throw "an if whose branches end at another height"
      return ([.cbz c (← cbField a aElse)] ++ ti ++ [.b (← bField aB aEnd)] ++ ei,
        some (h - 1 + ra))
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

/-- The frame of a function with `n` parameters and locals: 8 bytes for each and 8 for the
return address above them, rounded up to 16. -/
def frameSize (n : Nat) : Nat := (8 * (n + 1) + 15) / 16 * 16

/-- The number of instructions of the function `f`. -/
def functionSize (f : Function) : Nat :=
  2 + (f.params.length + f.locals.length) + (listSize [f.results.length] f.body).1 + 3

/-- The instructions of the function `f` placed at `entry`: the prologue, which allocates the
frame, saves the return address in X30 above the locals, and stores the parameters from X0 up and
zeros for the other locals, then the body, then the epilogue, which restores X30, frees the
frame, and returns. -/
def genFunction (trapUnreachable trapDiv entry : UInt64) (f : Function) : GenM (List Instr) := do
  let p := f.params.length
  let n := p + f.locals.length
  let r := f.results.length
  if p > 8 ∨ r > 1 then throw "a function with more than 8 parameters or 1 result"
  if hf : frameSize n < 4096 then
    have hn : n < 4096 := by unfold frameSize at hf; omega
    let bodyA := after entry (2 + n)
    let epilogue := after bodyA (listSize [r] f.body).1
    let E : Env := { locals := n, trapUnreachable, trapDiv }
    let (body, fin) ← genList E [{ target := epilogue, arity := r, base := 0 }] 0 bodyA f.body
    if fin.any (· ≠ r) then throw "a function body that ends at another height"
    let stores := List.ofFn fun i : Fin n =>
      Instr.str (if i.val < p then ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩ else 31) 31
        ⟨i.val, Nat.lt_trans i.isLt hn⟩
    return [.subImm 31 31 ⟨frameSize n, hf⟩, .str 30 31 ⟨n, hn⟩] ++ stores ++ body ++
      [.ldr 30 31 ⟨n, hn⟩, .addImm 31 31 ⟨frameSize n, hf⟩, .ret 30]
  else throw s!"a frame of {frameSize n} bytes"

/-- The number of instructions of `main` for `k` arguments. -/
def mainSize (k : Nat) : Nat := 2 + 4 * k + 1 + 4 + 16 + 4 + 3

/-- `main` placed at `a`: it calls the function at `entry` with `args`, writes the eight bytes of
the result to the UART at `uart`, the lowest first, and returns 0. -/
def genMain (a entry : UInt64) (args : List UInt64) (uart : UInt64) : GenM (List Instr) := do
  if args.length > 8 then throw "more than 8 arguments"
  let loads := args.zipIdx.flatMap fun (v, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ v
  let writes := (List.range 8).flatMap fun i =>
    [Instr.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩, .strb 2 1 0]
  let call := Instr.bl (← bField (after a (2 + 4 * args.length)) entry)
  return [.subImm 31 31 16, .str 30 31 0] ++ loads ++ [call] ++ movImm 1 uart ++ writes ++
    movImm 0 0 ++ [.ldr 30 31 0, .addImm 31 31 16, .ret 30]

/-- The program that runs function `k` of `m` on `args`, placed after its exit word at `base`:
`main` at `base + 4`, the function, and the trap stubs of codes 1, 2, and 3, each `movImm` of
X0 and a branch to the exit word.  The image puts a branch to `lx_exit` at `base`. -/
def genProgram (m : Module) (k : Nat) (args : List UInt64) (uart base : UInt64) :
    GenM (List Instr) := do
  let f ← match m.funcs[k]? with
    | some f => pure f
    | none => throw s!"no function {k}"
  let mainA := after base 1
  let entry := after mainA (mainSize args.length)
  let traps := after entry (functionSize f)
  let main ← genMain mainA entry args uart
  let fn ← genFunction traps (after traps 10) entry f
  let stub (a : UInt64) (code : Nat) : GenM (List Instr) := do
    return movImm 0 (UInt64.ofNat code) ++ [.b (← bField (after a 4) base)]
  return main ++ fn ++ (← stub traps 1) ++ (← stub (after traps 5) 2) ++
    (← stub (after traps 10) 3)

end LeanExe.A64
