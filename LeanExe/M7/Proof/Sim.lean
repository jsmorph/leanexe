import LeanExe.M7.Proof.Store
import LeanExe.M7.Div
import LeanExe.ProofKit.AlignedDefs

/-!
The simulation of Talos's `execOne` and `exec` by the generated Cortex-M7 code, as the AArch64
back end states it in `LeanExe/A64/Proof/Sim.lean`.  `Outcome` relates Talos's continuation for an
instruction or an instruction list to what the model does from a related state at the start of
its code, with SP, the device trace, the read count, the word of the LR slot, and the bytes from
the end of the parameters up as they were.  A fall-through reaches the end of the code in a
related state with the operand slots below the innermost construct's base unchanged.  A branch
`k` levels out reaches the target of the `k`-th enclosing construct with the values that it
carries in the slots from the target's base height, the slots below that height unchanged, and
the locals in their slots, and a return reaches the function's epilogue with the returned values
in the slots from height 0.  Each of the three holds Talos's store in the area, which `StoreOk`
states for a program with an area and leaves empty for a program without one.  A trap, an
invalid state, and the end of the fuel give no claim, since the board's theorems exclude traps
through the compiler's theorem without a trap.

`coveredInstr` and `coveredList` name the forms whose simulation is proved, which the kernel's
evaluation of `reachCovered` checks for each step.  `InstrSim F inst` states the simulation of
`inst` at fuel `F` for every placement at an even address that the generator gives it, from a
state whose stack holds at least `D` bytes below SP, where `D` bounds the stack of each call that
`inst` makes.  The address is even because `BL` sets LR to the next address with bit 0 set, and the
return to LR with bit 0 cleared reaches that address only when it is even.  For a program with an
area, the premises add that the module's memory has 32-bit addresses and that Talos's run makes
only aligned 64-bit accesses inside memory, `AlignedOne` of `LeanExe/ProofKit/AlignedDefs.lean`,
so that each access's two words are aligned.  `FunSim` states the simulation of a call of a
function from its entry, with the arguments in the caller's outgoing area, and `CallsOk` that
every function of a table satisfies it below a fuel.  `DivAt` places the code of `udivmod64` at the
address that the functions share, whose theorem `udivmod64_spec` the simulation of `divUI64` and
`remUI64` uses.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16)

/-! ## The covered forms -/

mutual
/-- The forms whose simulation is proved. -/
def coveredInstr : Instruction → Bool
  | .localGet _ | .localSet _ | .constI64 _ | .andI64 | .orI64 | .xorI64 | .addI64 | .subI64
  | .mulI64 | .eqI64 | .neI64 | .ltUI64 | .leUI64 | .geUI64 | .eqzI64 | .extendUI32 | .wrapI64
  | .shlI64 | .shrUI64 | .divUI64 | .remUI64 | .load64 _ | .store64 _ | .globalGet _
  | .globalSet _ | .br _ | .br_if _ | .ret | .call _ => true
  | .block _ _ body _ _ | .loop _ _ body _ _ => coveredList body
  | .iff _ _ thn els _ _ => coveredList thn && coveredList els
  | _ => false

/-- Every instruction of `is` is covered. -/
def coveredList : List Instruction → Bool
  | [] => true
  | i :: rest => coveredInstr i && coveredList rest
end

/-- The code of `udivmod64` lies at the address that the functions of a program share. -/
def DivAt (code : UInt32 → Option UInt16) (S : Shared) : Prop := CodeAt code S.udivmod udivmod64

/-! ## The store -/

/-- For a program with an area, the machine holds Talos's store there as `StoreRel` states it,
below the stack's limit; a program without one has no such clause. -/
def StoreOk (S : Shared) {α : Type} (st : Store α) (s : State) : Prop :=
  ∀ A, S.area = some A → StoreRel P areaHeader S.limit areaPages A.globals st s

/-- The bytes below the stack's limit `lim` keep in `t` their values in `s`. -/
def KeepsBelow (lim : UInt32) (s t : State) : Prop :=
  ∀ a : UInt32, a.toNat < lim.toNat → t.mem a = s.mem a

theorem KeepsBelow.refl (lim : UInt32) (s : State) : KeepsBelow lim s s := fun _ _ => rfl

theorem KeepsBelow.trans {lim : UInt32} {s t u : State} (h1 : KeepsBelow lim s t)
    (h2 : KeepsBelow lim t u) : KeepsBelow lim s u :=
  fun a ha => (h2 a ha).trans (h1 a ha)

theorem KeepsBelow.of_mem {lim : UInt32} {s t : State} (h : t.mem = s.mem) : KeepsBelow lim s t :=
  fun _ _ => by rw [h]

theorem StoreOk.congr {P : Platform} {S : Shared} {α : Type} {st : Store α} {s t : State}
    (h : StoreOk P S st s) (hk : KeepsBelow S.limit s t) : StoreOk P S st t :=
  fun A hA => (h A hA).congr hk

/-! ## Aligned runs -/

theorem alignedExec_head {α : Type} {F : Nat} {m : Module} {st : Store α} {sl : Locals}
    {i : Instruction} {rest : Program} {env : HostEnv α} (h : AlignedExec F m st sl (i :: rest) env) :
    AlignedOne F m st sl i env := by
  simp only [AlignedExec] at h
  exact h.1

theorem alignedExec_tail {α : Type} {F : Nat} {m : Module} {st st' : Store α} {sl sl' : Locals}
    {i : Instruction} {rest : Program} {env : HostEnv α}
    (h : AlignedExec F m st sl (i :: rest) env)
    (hr : execOne F m st sl i env = .Fallthrough st' sl') : AlignedExec F m st' sl' rest env := by
  simp only [AlignedExec, hr] at h
  exact h.2

theorem alignedOne_call {α : Type} {f : Nat} {m : Module} {st : Store α} {sl : Locals} {k : Nat}
    {env : HostEnv α} (h : AlignedOne (f + 1) m st sl (.call k) env) :
    AlignedRun f m k st sl.values env := by
  simp only [AlignedOne] at h
  exact h

theorem alignedOne_iff {α : Type} {f pa ra : Nat} {m : Module} {st : Store α} {sl : Locals}
    {thn els : Program} {pts rts : List ValueType} {env : HostEnv α} {c : UInt32}
    {vs : List Value} (h : AlignedOne (f + 1) m st sl (.iff pa ra thn els pts rts) env)
    (hv : sl.values = .i32 c :: vs) :
    AlignedExec f m st { sl with values := vs } (if c ≠ 0 then thn else els) env := by
  simp only [AlignedOne, hv] at h
  exact h

theorem alignedOne_block {α : Type} {f pa ra : Nat} {m : Module} {st : Store α} {sl : Locals}
    {body : Program} {pts rts : List ValueType} {env : HostEnv α}
    (h : AlignedOne (f + 1) m st sl (.block pa ra body pts rts) env) :
    AlignedExec f m st sl body env := by
  simp only [AlignedOne] at h
  exact h

/-- The aligned run of a loop is its body's and, after a branch back to the loop's head, the
loop's from the next state at one less fuel. -/
theorem alignedOne_loop {α : Type} {f pa ra : Nat} {m : Module} {st : Store α} {sl : Locals}
    {body : Program} {pts rts : List ValueType} {env : HostEnv α}
    (h : AlignedOne (f + 1) m st sl (.loop pa ra body pts rts) env) :
    AlignedExec f m st sl body env ∧
      ∀ st' sl', Wasm.exec f m st sl body env = .Break 0 st' sl' →
        AlignedOne f m st' { sl' with values := sl'.values.take pa ++ sl.values.drop pa }
          (.loop pa ra body pts rts) env := by
  simp only [AlignedOne] at h
  refine ⟨h.1, fun st' sl' he => ?_⟩
  have h2 := h.2
  rw [he] at h2
  exact h2

theorem alignedOne_load64 {α : Type} {f : Nat} {m : Module} {st : Store α} {sl : Locals}
    {off : UInt32} {env : HostEnv α} (h : AlignedOne (f + 1) m st sl (.load64 off) env) :
    (∀ a vs, sl.values = .i32 a :: vs → a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
      (a.toNat + off.toNat) % 8 = 0) ∧
    (∀ a vs, sl.values = .i64 a :: vs → a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
      (a.toUInt32.toNat + off.toNat) % 8 = 0) := by
  refine ⟨fun a vs hv => ?_, fun a vs hv => ?_⟩ <;> simp only [AlignedOne, hv] at h <;> exact h

theorem alignedOne_store64 {α : Type} {f : Nat} {m : Module} {st : Store α} {sl : Locals}
    {off : UInt32} {env : HostEnv α} (h : AlignedOne (f + 1) m st sl (.store64 off) env) :
    (∀ v a vs, sl.values = .i64 v :: .i32 a :: vs → a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 →
      (a.toNat + off.toNat) % 8 = 0) ∧
    (∀ v a vs, sl.values = .i64 v :: .i64 a :: vs →
      a.toNat + off.toNat + 8 ≤ st.mem.pages * 65536 → (a.toUInt32.toNat + off.toNat) % 8 = 0) := by
  refine ⟨fun v a vs hv => ?_, fun v a vs hv => ?_⟩ <;> simp only [AlignedOne, hv] at h <;>
    exact h

/-! ## Branches -/

/-- The enclosing constructs, the function's last, with their bases at or below the innermost
one's. -/
structure CtlOk (ctl : List Ctl) : Prop where
  nonempty : ctl ≠ []
  bases : ∀ t ∈ ctl, t.base ≤ curBase ctl

/-- The values that a branch to `t` carries, the first `t.arity` of `vs`, top first, lie in the
operand slots of the frame `fr` from the height `t.base` up. -/
structure Kept (fr : Frame) (t : Ctl) (vs : List Value) (s : State) : Prop where
  len : t.arity ≤ vs.length
  fits : t.base + t.arity ≤ fr.height
  vals : ∀ j (hj : j < t.arity), ValAt s (fr.opAt (t.base + j)) (vs[t.arity - 1 - j]'(by omega))
  types : Typed t.types (vs.take t.arity)

/-- The slots of the parameters and of the named locals hold the values `ls` of the locals, which
have the locals' types. -/
structure LocalsOk (E : Env) (ls : List Value) (s : State) : Prop where
  count : ls.length = E.localTypes.length
  vals : ∀ i v o, ls[i]? = some v → E.frame.localOff i = some o → ValAt s o v
  types : ∀ i v t o, ls[i]? = some v → E.localTypes[i]? = some t →
    E.frame.localOff i = some o → HasType t v

theorem Inv.localsOk {P : Platform} {E : Env} {σs : List ValueType} {sl : Locals} {s : State}
    (h : Inv P E σs sl s) : LocalsOk E (sl.params ++ sl.locals) s :=
  ⟨h.count, h.locals, h.ltypes⟩

/-! ## Outcomes -/

/-- What the model does from `ms` at the code of an instruction or a list, whose end is `endA`,
when Talos gives `r`: `fin` is the types of the operand stack after the code, `none` when its end
is unreachable. -/
def Outcome (E : Env) (ctl : List Ctl) (fin : Option (List ValueType)) (endA : UInt32)
    {α : Type} (r : Continuation α) (ms : State) : Prop :=
  match r with
  | .Fallthrough st' sl' => ∃ σ', fin = some σ' ∧ ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = endA ∧
      ms'.sp = ms.sp ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      BodyKeeps E.frame ms.sp ms ms' ∧ Below E.frame (curBase ctl) ms ms' ∧ Inv P E σ' sl' ms' ∧
      StoreOk P E.toShared st' ms'
  | .Break k st' sl' => ∃ t, ctl[k]? = some t ∧ ∃ ms', Reach P σ code ms ms' ∧
      ms'.pc = t.target ∧ ms'.sp = ms.sp ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      BodyKeeps E.frame ms.sp ms ms' ∧ Below E.frame t.base ms ms' ∧
      LocalsOk E (sl'.params ++ sl'.locals) ms' ∧ Kept E.frame t sl'.values ms' ∧
      StoreOk P E.toShared st' ms'
  | .Return st' vs => ∃ t, ctl.getLast? = some t ∧ ∃ ms', Reach P σ code ms ms' ∧
      ms'.pc = t.target ∧ ms'.sp = ms.sp ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      BodyKeeps E.frame ms.sp ms ms' ∧ Kept E.frame t vs ms' ∧ StoreOk P E.toShared st' ms'
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
results up unchanged, the results in the outgoing area, and the final store in the area of a
program with one. -/
def CallResult (S : Shared) (ps rs : List ValueType) (vs : List Value) {α : Type} (res : Result α)
    (ms : State) : Prop :=
  match res with
  | .Success vs' st' => ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧
      ms'.sp = ms.sp ∧ ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 8 * max ps.length rs.length ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      vs'.length = rs.length + (vs.length - ps.length) ∧ vs'.drop rs.length = vs.drop ps.length ∧
      ArgsAt ms' (vs'.take rs.length) ∧ Typed rs.reverse (vs'.take rs.length) ∧
      StoreOk P S st' ms'
  | .Trap _ _ => True
  | .Invalid _ => True
  | .OutOfFuel => True
  | .Thrown _ _ _ => False

/-- The simulation of a call of function `k` of `m`, whose entry and the types of whose
parameters and results `c` gives, at fuel `g`: from the entry, with bit 0 of LR set, the stack of
`StackOk` for `need k` bytes, the top values of the operand stack `vs`, of the parameters' types,
in the outgoing area, and the store in the area of a program with one, whose module has 32-bit
addresses and whose run of the call makes only aligned accesses, the model does what `CallResult`
states of Talos's run of the call. -/
def FunSim (m : Module) (S : Shared) (need : Nat → Nat) (g k : Nat)
    (c : UInt32 × List ValueType × List ValueType) : Prop :=
  ∀ {α : Type} (st : Store α) (vs : List Value) (ms : State), c.2.1.length ≤ vs.length →
    Typed c.2.1.reverse (vs.take c.2.1.length) → ms.pc = c.1 → ms.lr % 2 = 1 →
    StackOk P S.limit (max c.2.1.length c.2.2.length) (need k) ms →
    ArgsAt ms (vs.take c.2.1.length) → StoreOk P S st ms →
    (S.area.isSome = true → m.memIs64 = false ∧ AlignedRun g m k st vs {}) →
    CallResult P σ code S c.2.1 c.2.2 vs (Wasm.run g m k st vs) ms

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
    DivAt code E.toShared → curBase ctl ≤ σs.length → CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E σs sl ms → StoreOk P E.toShared st ms → ms.pc = a →
      (E.area.isSome = true → m.memIs64 = false ∧ AlignedOne F m st sl inst {}) →
      ∀ (need : Nat → Nat) (D : Nat),
      CallsOk P σ code F m E.callee E.toShared need → (∀ j ∈ callsOf inst, need j ≤ D) →
      D ≤ room E ms → Outcome P σ code E ctl fin (after a is.length) (execOne F m st sl inst) ms

/-- The simulation of instruction lists at fuel `F`. -/
def ListSim (F : Nat) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σs : List ValueType) (a : UInt32) (p : List Instruction)
    (is : List Instr) (fin : Option (List ValueType)), coveredList p = true →
    genList E ctl σs a p = .ok (is, fin) → CodeAt code a is → a.toNat % 2 = 0 →
    DivAt code E.toShared → curBase ctl ≤ σs.length → CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E σs sl ms → StoreOk P E.toShared st ms → ms.pc = a →
      (E.area.isSome = true → m.memIs64 = false ∧ AlignedExec F m st sl p {}) →
      ∀ (need : Nat → Nat) (D : Nat),
      CallsOk P σ code F m E.callee E.toShared need → (∀ j ∈ callsIn p, need j ≤ D) →
      D ≤ room E ms → Outcome P σ code E ctl fin (after a is.length) (Wasm.exec F m st sl p) ms

end LeanExe.M7
