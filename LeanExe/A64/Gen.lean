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
registers of the construct's base height and branches to the construct's label: the end of a
`block` or an `iff`, the start of a `loop`, or the epilogue for the function itself, which also
serves `ret`.  The result lies at height 0, in X0, when the epilogue releases the frame and
returns.  Code after a `br`, a `ret`, or `unreachable` in the same list is unreachable, and the
generator emits nothing for it.  A trap branches to a stub that sets X0 to the trap's code of
`LeanExe.Native.trapCode`, 1, 2, or 3, and branches to `lx_exit` of the startup code.

`layout` places the items at an address, gives each label the address of the next instruction,
and encodes each branch with its offset after checking the offset's range.
-/

namespace LeanExe.A64

open Wasm

/-- An item of generated code before layout. -/
inductive Item where
  /-- An instruction. -/
  | ins (i : Instr)
  /-- A label, which takes the address of the next instruction. -/
  | label (l : Nat)
  /-- `B` to a label. -/
  | b (l : Nat)
  /-- `BL` to a label. -/
  | bl (l : Nat)
  /-- `CBZ` of a register to a label. -/
  | cbz (r : Fin 32) (l : Nat)
  /-- `CBNZ` of a register to a label. -/
  | cbnz (r : Fin 32) (l : Nat)
  /-- `B` to `lx_exit` of the startup code. -/
  | exit
  deriving Repr

/-- The registers of the operand stack's heights. -/
def opRegs : List Nat := List.range 16 ++ (List.range 10).map (· + 19)

/-- The scratch register. -/
def scratch : Fin 32 := 16

abbrev GenM := StateT Nat (Except String)

/-- A label that no other item uses. -/
def fresh : GenM Nat := modifyGet fun n => (n, n + 1)

/-- The register of height `h`. -/
def opReg (h : Nat) : GenM (Fin 32) :=
  match opRegs[h]? with
  | some r => pure ⟨r % 32, Nat.mod_lt _ (by decide)⟩
  | none => throw s!"an operand stack deeper than {opRegs.length} values"

/-- Bits `16 * k` to `16 * k + 15` of `v`. -/
def half (v : UInt64) (k : Nat) : Fin 65536 :=
  ⟨v.toNat / 65536 ^ k % 65536, Nat.mod_lt _ (by decide)⟩

/-- Sets register `d` to `v` with `MOVZ` and three `MOVK`. -/
def movImm (d : Fin 32) (v : UInt64) : List Item :=
  [.ins (.movz d (half v 0) 0), .ins (.movk d (half v 1) 1), .ins (.movk d (half v 2) 2),
    .ins (.movk d (half v 3) 3)]

/-- Copies register `s` to register `d`, or nothing when they are the same. -/
def mov (d s : Fin 32) : List Item :=
  if d = s then [] else [.ins (.orrReg d 31 s)]

/-- The frame slot of local `i`, as the scaled offset of `LDR` and `STR`. -/
def slotOf (i : Nat) : GenM (Fin 4096) :=
  if h : i < 4096 then pure ⟨i, h⟩ else throw s!"local {i} lies beyond the frame's reach"

/-- A construct that a branch can target: its label, the number of values that a branch to it
carries, and the height under those values at the label. -/
structure Ctl where
  label : Nat
  arity : Nat
  base : Nat

/-- What the instructions of one function need: the number of its locals, parameters
included, and the labels of the traps at `unreachable` and at a division by zero. -/
structure Env where
  locals : Nat
  trapUnreachable : Nat
  trapDiv : Nat

/-- The moves of a branch to `t` from height `h`, and the branch. -/
def branchTo (t : Ctl) (h : Nat) : GenM (List Item) := do
  if h < t.base + t.arity then throw "a branch with fewer values than its target takes"
  let mut moves := []
  for i in [0:t.arity] do
    moves := moves ++ mov (← opReg (t.base + i)) (← opReg (h - t.arity + i))
  return moves ++ [.b t.label]

mutual
/-- The items of the instruction `ins` at height `h` under the constructs `ctl`, and the height
after it, or `none` when the code after it is unreachable. -/
def genInstr (E : Env) (ctl : List Ctl) (h : Nat) :
    Instruction → GenM (List Item × Option Nat)
  | .localGet i => do
      if i ≥ E.locals then throw s!"local {i} of {E.locals}"
      return ([.ins (.ldr (← opReg h) 31 (← slotOf i))], some (h + 1))
  | .localSet i => do
      if i ≥ E.locals ∨ h = 0 then throw s!"local.set {i} at height {h}"
      return ([.ins (.str (← opReg (h - 1)) 31 (← slotOf i))], some (h - 1))
  | .localTee i => do
      if i ≥ E.locals ∨ h = 0 then throw s!"local.tee {i} at height {h}"
      return ([.ins (.str (← opReg (h - 1)) 31 (← slotOf i))], some h)
  | .constI64 v => do return (movImm (← opReg h) v, some (h + 1))
  | .const v => do return (movImm (← opReg h) v.toUInt64, some (h + 1))
  | .eqI64 | .eq => do
      if h < 2 then throw s!"a comparison at height {h}"
      let a ← opReg (h - 2)
      return ([.ins (.subsReg 31 a (← opReg (h - 1))), .ins (.csinc a 31 31 1)], some (h - 1))
  | .eqzI64 | .eqz => do
      if h < 1 then throw "eqz at height 0"
      let a ← opReg (h - 1)
      return ([.ins (.subsImm 31 a 0), .ins (.csinc a 31 31 1)], some h)
  | .extendUI32 => do
      if h < 1 then throw "extend at height 0"
      return ([], some h)
  | .remUI64 => do
      if h < 2 then throw s!"a remainder at height {h}"
      let a ← opReg (h - 2)
      let b ← opReg (h - 1)
      return ([.cbz b E.trapDiv, .ins (.udiv scratch a b), .ins (.msub a scratch b a)],
        some (h - 1))
  | .divUI64 => do
      if h < 2 then throw s!"a division at height {h}"
      let a ← opReg (h - 2)
      let b ← opReg (h - 1)
      return ([.cbz b E.trapDiv, .ins (.udiv a a b)], some (h - 1))
  | .unreachable => return ([.b E.trapUnreachable], none)
  | .br n => do
      match ctl[n]? with
      | some t => return (← branchTo t h, none)
      | none => throw s!"br {n} under {ctl.length} constructs"
  | .br_if n => do
      if h < 1 then throw "br_if at height 0"
      match ctl[n]? with
      | some t =>
          let c ← opReg (h - 1)
          if t.arity = 0 then return ([.cbnz c t.label], some (h - 1))
          let skip ← fresh
          return ([.cbz c skip] ++ (← branchTo t (h - 1)) ++ [.label skip], some (h - 1))
      | none => throw s!"br_if {n} under {ctl.length} constructs"
  | .ret => do
      match ctl.getLast? with
      | some t => return (← branchTo t h, none)
      | none => throw "ret outside a function"
  | .block pa ra body _ _ => do
      if pa ≠ 0 then throw "a block with parameters"
      let l ← fresh
      let (items, after) ← genList E ({ label := l, arity := ra, base := h } :: ctl) h body
      if after.any (· ≠ h + ra) then throw "a block that ends at another height"
      return (items ++ [.label l], some (h + ra))
  | .loop pa ra body _ _ => do
      if pa ≠ 0 then throw "a loop with parameters"
      let l ← fresh
      let (items, after) ← genList E ({ label := l, arity := 0, base := h } :: ctl) h body
      if after.any (· ≠ h + ra) then throw "a loop that ends at another height"
      return (.label l :: items, after)
  | .iff pa ra thn els _ _ => do
      if pa ≠ 0 ∨ h < 1 then throw "an if with parameters or without a condition"
      let c ← opReg (h - 1)
      let lElse ← fresh
      let lEnd ← fresh
      let inner := { label := lEnd, arity := ra, base := h - 1 } :: ctl
      let (ti, ta) ← genList E inner (h - 1) thn
      let (ei, ea) ← genList E inner (h - 1) els
      if ta.any (· ≠ h - 1 + ra) ∨ ea.any (· ≠ h - 1 + ra) then
        throw "an if whose branches end at another height"
      let after := if ta.isSome ∨ ea.isSome then some (h - 1 + ra) else none
      return ([.cbz c lElse] ++ ti ++ (if ta.isSome then [.b lEnd] else []) ++
        [.label lElse] ++ ei ++ [.label lEnd], after)
  | i => throw s!"the form {repr i} lies outside the generator's forms"

/-- The items of the instructions `is` at height `h` under the constructs `ctl`, and the height
after them, or `none` when their end is unreachable. -/
def genList (E : Env) (ctl : List Ctl) (h : Nat) :
    List Instruction → GenM (List Item × Option Nat)
  | [] => return ([], some h)
  | i :: rest => do
      let (a, after) ← genInstr E ctl h i
      match after with
      | none => return (a, none)
      | some h' =>
          let (b, after') ← genList E ctl h' rest
          return (a ++ b, after')
end

/-- The items of the function `f` from its label `entry`. -/
def genFunction (trapUnreachable trapDiv entry : Nat) (f : Function) : GenM (List Item) := do
  let p := f.params.length
  let n := p + f.locals.length
  let r := f.results.length
  if p > 8 ∨ r > 1 then throw "a function with more than 8 parameters or 1 result"
  let frame := (8 * n + 15) / 16 * 16
  if hf : frame < 4096 then
    let lret ← fresh
    let E : Env := { locals := n, trapUnreachable, trapDiv }
    let (body, after) ← genList E [{ label := lret, arity := r, base := 0 }] 0 f.body
    if after.any (· ≠ r) then throw "a function body that ends at another height"
    let mut prologue := [.label entry, .ins (.subImm 31 31 ⟨frame, hf⟩)]
    for i in [0:n] do
      let src : Fin 32 := if i < p then ⟨i % 32, Nat.mod_lt _ (by decide)⟩ else 31
      prologue := prologue ++ [.ins (.str src 31 (← slotOf i))]
    return prologue ++ body ++ [.label lret, .ins (.addImm 31 31 ⟨frame, hf⟩), .ins (.ret 30)]
  else throw s!"a frame of {frame} bytes"

/-- `main`: it calls the function at `entry` with `args`, writes the eight bytes of the result to
the UART at `uart`, the lowest first, and returns 0. -/
def genMain (entry : Nat) (args : List UInt64) (uart : UInt64) : GenM (List Item) := do
  if args.length > 8 then throw "more than 8 arguments"
  let loads := args.zipIdx.flatMap fun (a, i) => movImm ⟨i % 32, Nat.mod_lt _ (by decide)⟩ a
  let writes := (List.range 8).flatMap fun i =>
    [Item.ins (.lsrImm 2 0 ⟨8 * i % 64, Nat.mod_lt _ (by decide)⟩), .ins (.strb 2 1 0)]
  return [.ins (.subImm 31 31 16), .ins (.str 30 31 0)] ++ loads ++ [.bl entry] ++
    movImm 1 uart ++ writes ++ movImm 0 0 ++
    [.ins (.ldr 30 31 0), .ins (.addImm 31 31 16), .ins (.ret 30)]

/-- The program that runs function `k` of `m` on `args`: `main`, the function, and the trap
stubs, in that order. -/
def genProgram (m : Module) (k : Nat) (args : List UInt64) (uart : UInt64) :
    Except String (List Item) :=
  (do
    let trapUnreachable ← fresh
    let trapBounds ← fresh
    let trapDiv ← fresh
    let entry ← fresh
    let f ← match m.funcs[k]? with
      | some f => pure f
      | none => throw s!"no function {k}"
    let main ← genMain entry args uart
    let fn ← genFunction trapUnreachable trapDiv entry f
    let stub (l code : Nat) : List Item :=
      [Item.label l] ++ movImm 0 (UInt64.ofNat code) ++ [Item.exit]
    return main ++ fn ++ stub trapUnreachable 1 ++ stub trapBounds 2 ++ stub trapDiv 3).run' 0

/-- A placed word: an instruction's encoding, or the branch to `lx_exit`. -/
inductive Word where
  | inst (w : UInt32)
  | exit
  deriving Repr, BEq

/-- The addresses of the labels of `items` placed from `base`. -/
def labels (base : UInt64) (items : List Item) : List (Nat × UInt64) :=
  (items.foldl (fun (acc, a) it => match it with
    | .label l => ((l, a) :: acc, a)
    | _ => (acc, a + 4)) ([], base)).1

/-- The field of `bits` bits of a branch from `here` to `target`, when the offset fits. -/
def branchField (bits : Nat) (here target : UInt64) : Except String Nat := do
  let off := (Int.ofNat target.toNat - Int.ofNat here.toNat) / 4
  if (Int.ofNat target.toNat - Int.ofNat here.toNat) % 4 ≠ 0 ∨ off < -(2 ^ (bits - 1)) ∨
      off ≥ 2 ^ (bits - 1) then
    throw s!"a branch from {here} to {target} beyond {bits} bits"
  return (off % (2 ^ bits : Int)).toNat

/-- The words of `items` placed from `base`. -/
def layout (base : UInt64) (items : List Item) : Except String (List Word) := do
  let ls := labels base items
  let addr (l : Nat) : Except String UInt64 :=
    match ls.lookup l with
    | some a => pure a
    | none => throw s!"label {l} is not placed"
  let mut out := #[]
  let mut here := base
  for it in items do
    match it with
    | .label _ => continue
    | .ins i => out := out.push (.inst (encode i))
    | .exit => out := out.push .exit
    | .b l =>
        let f ← branchField 26 here (← addr l)
        out := out.push (.inst (encode (.b ⟨f % 67108864, Nat.mod_lt _ (by decide)⟩)))
    | .bl l =>
        let f ← branchField 26 here (← addr l)
        out := out.push (.inst (encode (.bl ⟨f % 67108864, Nat.mod_lt _ (by decide)⟩)))
    | .cbz r l =>
        let f ← branchField 19 here (← addr l)
        out := out.push (.inst (encode (.cbz r ⟨f % 524288, Nat.mod_lt _ (by decide)⟩)))
    | .cbnz r l =>
        let f ← branchField 19 here (← addr l)
        out := out.push (.inst (encode (.cbnz r ⟨f % 524288, Nat.mod_lt _ (by decide)⟩)))
    here := here + 4
  return out.toList

end LeanExe.A64
