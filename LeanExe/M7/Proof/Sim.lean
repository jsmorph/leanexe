import LeanExe.M7.Proof.Relation
import LeanExe.M7.Div

/-!
The simulation of Talos's `execOne` and `exec` by the generated Cortex-M7 code, as the AArch64
back end states it in `LeanExe/A64/Proof/Sim.lean`.  `Outcome` relates Talos's continuation for an
instruction or an instruction list to what the model does from a related state at the start of
its code: a fall-through reaches the end of the code in a related state, with SP, the device
trace, and the read count as they were, the word of the LR slot and the bytes from the end of the
parameters up unchanged, and the operand slots below the innermost construct's base unchanged.
A trap, an invalid state, and the end of the fuel give no claim, since the board's theorems
exclude traps through the compiler's theorem without a trap.  The functions that the echo's and
the gateway's steps reach contain no `br`, `br_if`, `return`, or `loop` (`devnotes.md`, G0), so a
branch out of a construct and a return have the outcome `False`, which the covered forms never
give.

`coveredInstr` and `coveredList` name the forms whose simulation this increment proves: the forms
of the functions that the echo's steps reach, with `divUI64`.  `InstrSim F inst` states the simulation of `inst` at fuel
`F` for every placement at an even address that the generator gives it, from a state whose stack
holds at least `D` bytes below SP, where `D` bounds the stack of each call that `inst` makes.  The
address is even because `BL` sets LR to the next address with bit 0 set, and the return to LR
with bit 0 cleared reaches that address only when it is even.  `FunSim` states the simulation of a
call of a function from its entry, with the arguments in the caller's outgoing area, and `CallsOk`
that every function of a table satisfies it below a fuel.  `DivAt` places the code of `udivmod64`
at the address that the functions share, whose theorem `udivmod64_spec` the simulation of
`divUI64` and `remUI64` uses.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16)

/-! ## The covered forms -/

mutual
/-- The forms whose simulation this increment proves. -/
def coveredInstr : Instruction → Bool
  | .localGet _ | .localSet _ | .constI64 _ | .andI64 | .orI64 | .xorI64 | .addI64 | .mulI64
  | .eqI64 | .neI64 | .eqzI64 | .extendUI32 | .shlI64 | .shrUI64 | .divUI64 | .remUI64
  | .call _ => true
  | .iff _ _ thn els _ _ => coveredList thn && coveredList els
  | _ => false

/-- Every instruction of `is` is covered. -/
def coveredList : List Instruction → Bool
  | [] => true
  | i :: rest => coveredInstr i && coveredList rest
end

/-- The code of `udivmod64` lies at the address that the functions of a program share. -/
def DivAt (code : UInt32 → Option UInt16) (S : Shared) : Prop := CodeAt code S.udivmod udivmod64

/-! ## Outcomes -/

/-- What the model does from `ms` at the code of an instruction or a list, whose end is `endA`,
when Talos gives `r`: `fin` is the types of the operand stack after the code, `none` when its end
is unreachable. -/
def Outcome (E : Env) (ctl : List Ctl) (fin : Option (List ValueType)) (endA : UInt32)
    {α : Type} (r : Continuation α) (ms : State) : Prop :=
  match r with
  | .Fallthrough _ sl' => ∃ σ', fin = some σ' ∧ ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = endA ∧
      ms'.sp = ms.sp ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      BodyKeeps E.frame ms.sp ms ms' ∧ Below E.frame (curBase ctl) ms ms' ∧ Inv P E σ' sl' ms'
  | .Break _ _ _ => False
  | .Return _ _ => False
  | .Trap _ _ => True
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-- The stack at SP for a call whose parameters and results take `n` slots of the caller's
outgoing area at SP and whose stack needs `need` bytes below SP: SP is a multiple of 4, the
outgoing area is `Ram` below 2^32, and the stack's limit `lim` lies from 4096 up to SP, at least
`need` bytes below it, with `Ram` from it to SP. -/
structure StackOk (lim : UInt32) (n need : Nat) (s : State) : Prop where
  aligned : s.sp % 4 = 0
  ram : ∀ j < 8 * n, Ram P (s.sp + UInt32.ofNat j)
  fits : s.sp.toNat + 8 * n ≤ 4294967296
  limit : 4096 ≤ lim.toNat ∧ lim.toNat ≤ s.sp.toNat
  below : ∀ j < s.sp.toNat - lim.toNat, Ram P (lim + UInt32.ofNat j)
  room : need ≤ s.sp.toNat - lim.toNat

/-- The values `vs`, top first, lie in the slots of the outgoing area at SP, the deepest in slot
0. -/
def ArgsAt (s : State) (vs : List Value) : Prop :=
  ∀ i v, vs.reverse[i]? = some v → ValAt s (8 * i) v

/-- What the model does from `ms` at the entry of a function with parameters of the types `ps`
and results of the types `rs`, called on the operand stack `vs`, when Talos's run of the call
gives `res`: a success returns to the address in LR with bit 0 clear, with SP, LR, the device
trace, and the read count as they were, every byte from SP plus the area of the parameters and
results up unchanged, and the results in the outgoing area. -/
def CallResult (ps rs : List ValueType) (vs : List Value) {α : Type} (res : Result α)
    (ms : State) : Prop :=
  match res with
  | .Success vs' _ => ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧
      ms'.sp = ms.sp ∧ ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 8 * max ps.length rs.length ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      vs'.length = rs.length + (vs.length - ps.length) ∧ vs'.drop rs.length = vs.drop ps.length ∧
      ArgsAt ms' (vs'.take rs.length) ∧ Typed rs.reverse (vs'.take rs.length)
  | .Trap _ _ => True
  | .Invalid _ => True
  | .OutOfFuel => True
  | .Thrown _ _ _ => False

/-- The simulation of a call of function `k` of `m`, whose entry and the types of whose
parameters and results `c` gives, at fuel `g`: from the entry, with bit 0 of LR set, the stack of
`StackOk` for `need k` bytes, and the top values of the operand stack `vs`, of the parameters'
types, in the outgoing area, the model does what `CallResult` states of Talos's run of the call. -/
def FunSim (m : Module) (S : Shared) (need : Nat → Nat) (g k : Nat)
    (c : UInt32 × List ValueType × List ValueType) : Prop :=
  ∀ {α : Type} (st : Store α) (vs : List Value) (ms : State), c.2.1.length ≤ vs.length →
    Typed c.2.1.reverse (vs.take c.2.1.length) → ms.pc = c.1 → ms.lr % 2 = 1 →
    StackOk P S.limit (max c.2.1.length c.2.2.length) (need k) ms →
    ArgsAt ms (vs.take c.2.1.length) →
    CallResult P σ code c.2.1 c.2.2 vs (Wasm.run g m k st vs) ms

/-- The functions of the table `callee` simulate at every fuel below `F` in module `m`. -/
def CallsOk (F : Nat) (m : Module) (callee : Table) (S : Shared) (need : Nat → Nat) : Prop :=
  ∀ k c, callee k = some c → ∀ g < F, FunSim P σ code m S need g k c

theorem CallsOk.mono {F G : Nat} {m : Module} {callee : Table} {S : Shared} {need : Nat → Nat}
    (h : CallsOk P σ code F m callee S need) (hle : G ≤ F) :
    CallsOk P σ code G m callee S need :=
  fun k c hk g hg => h k c hk g (by omega)

/-- The bytes of stack between the limit and SP. -/
def room (E : Env) (s : State) : Nat := s.sp.toNat - E.limit.toNat

/-- The simulation of `inst` at fuel `F`, from a state with at least `D` bytes of stack, for any
`D` at or above `need j` for each function `j` that `inst` calls. -/
def InstrSim (F : Nat) (inst : Instruction) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σs : List ValueType) (a : UInt32) (is : List Instr)
    (fin : Option (List ValueType)),
    genInstr E ctl σs a inst = .ok (is, fin) → CodeAt code a is → a.toNat % 2 = 0 →
    DivAt code E.toShared →
    curBase ctl ≤ σs.length →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E σs sl ms → ms.pc = a → ∀ (need : Nat → Nat) (D : Nat),
      CallsOk P σ code F m E.callee E.toShared need → (∀ j ∈ callsOf inst, need j ≤ D) →
      D ≤ room E ms → Outcome P σ code E ctl fin (after a is.length) (execOne F m st sl inst) ms

/-- The simulation of instruction lists at fuel `F`. -/
def ListSim (F : Nat) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σs : List ValueType) (a : UInt32) (p : List Instruction)
    (is : List Instr) (fin : Option (List ValueType)), coveredList p = true →
    genList E ctl σs a p = .ok (is, fin) → CodeAt code a is → a.toNat % 2 = 0 →
    DivAt code E.toShared →
    curBase ctl ≤ σs.length →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E σs sl ms → ms.pc = a → ∀ (need : Nat → Nat) (D : Nat),
      CallsOk P σ code F m E.callee E.toShared need → (∀ j ∈ callsIn p, need j ≤ D) →
      D ≤ room E ms → Outcome P σ code E ctl fin (after a is.length) (Wasm.exec F m st sl p) ms

end LeanExe.M7
