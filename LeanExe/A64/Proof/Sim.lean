import LeanExe.A64.Proof.Relation
import LeanExe.A64.Proof.Bits
import LeanExe.ProofKit.Locals

/-!
The simulation of Talos's `execOne` and `exec` by the generated code.  `Outcome` relates Talos's
continuation for an instruction or an instruction list to what the machine does from a related
state at the start of its code: a fall-through reaches the end of the code, a branch `k` levels
out reaches the target of the `k`-th enclosing construct with the values that the branch carries
in the registers of the target's base height, a return reaches the function's epilogue in the
same way, and a trap reaches the stub of its code.  Throughout, `SP`, the UART's output, and the
memory outside the function's frame keep their values.  `InstrSim F inst` states the simulation
of `inst` at fuel `F` for every placement that the generator gives it.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The bytes from the end of `n` slots at `sp` up keep their values from `s` to `s'`. -/
def MemFrame (sp : UInt64) (n : Nat) (s s' : State) : Prop :=
  ∀ a : UInt64, sp.toNat + 8 * n ≤ a.toNat → s'.mem a = s.mem a

/-- The values that a branch to `t` carries, the first `t.arity` of `vs`, top first, lie in the
registers of the heights from `t.base` up. -/
structure Kept (t : Ctl) (vs : List Value) (s : State) : Prop where
  len : t.arity ≤ vs.length
  fits : t.base + t.arity ≤ 26
  vals : ∀ j (hj : j < t.arity),
    ValRel (vs[t.arity - 1 - j]'(by omega)) (s.x (regOf (t.base + j)))
  types : Typed t.types (vs.take t.arity)

/-- The machine reaches the stub `tS` of a stack that a frame would overflow from `ms`, with the
UART's output as it was. -/
def Overflows (tS : UInt64) (ms : State) : Prop :=
  ∃ ms', Reach P code ms ms' ∧ ms'.pc = tS ∧ ms'.out = ms.out

/-- The table `callee` names a function, which a call may enter. -/
def HasCalls (callee : Table) : Prop :=
  ∃ k c, callee k = some c

/-- The trap with the message `msg` reaches its stub at `pc`: `unreachable`, an access outside the
memory, or a division by zero. -/
def TrapAt (tU tB tD : UInt64) (msg : String) (pc : UInt64) : Prop :=
  (msg = "unreachable" ∧ pc = tU) ∨ (msg = "out of bounds memory access" ∧ pc = tB) ∨
    (msg = "integer divide by zero" ∧ pc = tD)

/-- What the machine does from `ms` at the code of an instruction or a list, whose end is
`endA`, when Talos gives `r`, unless the function may call another and a call's frame would
overflow the stack: `fin` is the types of the operand stack after the code, `none` when its end
is unreachable.  SP, X18, and the UART's output keep their values, the bytes from the end of the
frame's spill slots up keep theirs, and the machine holds the store of every continuation that
continues the function. -/
def Outcome (E : Env) (ctl : List Ctl) (fin : Option (List ValueType)) (endA : UInt64)
    {α : Type} (r : Continuation α) (ms : State) : Prop :=
  (HasCalls E.callee ∧ Overflows P code E.trapStack ms) ∨
  match r with
  | .Fallthrough st' sl' => ∃ σ', fin = some σ' ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = endA ∧
      ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ ms'.x 18 = ms.x 18 ∧
      MemFrame ms.sp (E.locals + spillSlots) ms ms' ∧
      Inv P E.localTypes σ' sl' ms' ∧ Frame (curBase ctl) ms ms' ∧
      StoreRel P E.cap E.globalTypes st' ms'
  | .Break k st' sl' => ∃ t, ctl[k]? = some t ∧ ∃ ms', Reach P code ms ms' ∧
      ms'.pc = t.target ∧ ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ ms'.x 18 = ms.x 18 ∧
      MemFrame ms.sp (E.locals + spillSlots) ms ms' ∧
      LocalsRel ms' (sl'.params ++ sl'.locals) ∧ Typed E.localTypes (sl'.params ++ sl'.locals) ∧
      Kept t sl'.values ms' ∧ Frame t.base ms ms' ∧ StoreRel P E.cap E.globalTypes st' ms'
  | .Return st' vs => ∃ t, ctl.getLast? = some t ∧ ∃ ms', Reach P code ms ms' ∧
      ms'.pc = t.target ∧ ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ ms'.x 18 = ms.x 18 ∧
      MemFrame ms.sp (E.locals + spillSlots) ms ms' ∧ Kept t vs ms' ∧
      StoreRel P E.cap E.globalTypes st' ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      TrapAt E.trapUnreachable E.trapBounds E.trapDiv msg ms'.pc
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-- The enclosing constructs, the function's last, with their bases at or below the innermost
one's. -/
structure CtlOk (ctl : List Ctl) : Prop where
  nonempty : ctl ≠ []
  bases : ∀ t ∈ ctl, t.base ≤ curBase ctl

/-- What the machine does from `ms` at the entry of a function with parameters of the types `ps`
and results of the types `rs`, called on the operand stack `vs`, when Talos's run of the call
gives `res`: a success returns to the address in X30 with SP, X18, and the UART's output as they
were, the bytes from SP up unchanged, the results in the registers of the heights from 0, and the
final store in the area, and a trap reaches the stub of its code. -/
def CallResult (S : Shared) (ps rs : List ValueType) (vs : List Value) {α : Type}
    (res : Result α) (ms : State) : Prop :=
  match res with
  | .Success vs' st' => ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧
      ms'.x 18 = ms.x 18 ∧ ms'.out = ms.out ∧ MemFrame ms.sp 0 ms ms' ∧
      vs'.length = rs.length + (vs.length - ps.length) ∧
      vs'.drop rs.length = vs.drop ps.length ∧
      StackRel ms' (vs'.take rs.length) ∧ Typed rs.reverse (vs'.take rs.length) ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg ms'.pc
  | .Invalid _ => True
  | .OutOfFuel => True
  | .Thrown _ _ _ => False

/-- `CallResult`, or the machine reaches the stub of an overflow of the stack. -/
def CallOutcome (S : Shared) (ps rs : List ValueType) (vs : List Value) {α : Type}
    (res : Result α) (ms : State) : Prop :=
  Overflows P code S.trapStack ms ∨ CallResult P code S ps rs vs res ms

/-- The simulation of a call of function `k` of `m`, whose entry and the types of whose
parameters and results `c` gives, at fuel `g`: from the entry, with the stack's limit in X18,
the store in the area, and the top values of the operand stack `vs`, of the parameters' types, in
the registers of the heights from 0, the deepest first, the machine does what `CallOutcome`
states of Talos's run of the call. -/
def FunSim (m : Module) (S : Shared) (g k : Nat) (c : UInt64 × List ValueType × List ValueType) :
    Prop :=
  ∀ {α : Type} (st : Store α) (vs : List Value) (ms : State) (hp : c.2.1.length ≤ vs.length),
    Typed c.2.1.reverse (vs.take c.2.1.length) → ms.pc = c.1 → StackOk P ms →
    StoreRel P S.cap S.globalTypes st ms → StackRel ms (vs.take c.2.1.length) →
    CallOutcome P code S c.2.1 c.2.2 vs (Wasm.run g m k st vs) ms

/-- The functions of the table `callee` simulate at every fuel below `F` in module `m`, with what
the program's functions share `S`. -/
def CallsOk (F : Nat) (m : Module) (callee : Table) (S : Shared) : Prop :=
  ∀ k c, callee k = some c → ∀ g < F, FunSim P code m S g k c

theorem CallsOk.mono {F G : Nat} {m : Module} {callee : Table} {S : Shared}
    (h : CallsOk P code F m callee S) (hle : G ≤ F) : CallsOk P code G m callee S :=
  fun k c hk g hg => h k c hk g (by omega)

/-- The simulation of `inst` at fuel `F`. -/
def InstrSim (F : Nat) (inst : Instruction) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt64) (is : List Instr)
    (fin : Option (List ValueType)),
    genInstr E ctl σ a inst = .ok (is, fin) → CodeAt code a is → curBase ctl ≤ σ.length →
    CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E.localTypes σ sl ms → StoreRel P E.cap E.globalTypes st ms → m.memIs64 = false →
      ms.pc = a → CallsOk P code F m E.callee E.toShared →
      Outcome P code E ctl fin (after a is.length) (execOne F m st sl inst) ms

/-! ## Facts about states and the relation -/

namespace State

@[simp] theorem x_withPc (s : State) (p : UInt64) (r : Fin 32) :
    ({ s with pc := p } : State).x r = s.x r := rfl

theorem xsp_31 (s : State) : s.xsp 31 = s.sp := by
  unfold xsp; rw [dite_eq_right (by decide)]

end State

theorem ofNat_mul8 (i : Nat) : UInt64.ofNat (8 * i) = 8 * UInt64.ofNat i := by
  rw [UInt64.ofNat_mul]; rfl

theorem LocalsRel.congr {s s' : State} {ls : List Value} (h : LocalsRel s ls)
    (hmem : s'.mem = s.mem) (hsp : s'.sp = s.sp) : LocalsRel s' ls := by
  intro i hi
  rw [hmem, hsp]
  exact h i hi

/-- A load of local `i < n` from the frame of a related state passes the checks of `LDR`. -/
theorem mapped_slot {lts σ : List ValueType} {sl : Locals} {s : State} (hinv : Inv P lts σ sl s)
    {i : Nat} (hi : i < lts.length) : P.mapped (s.sp + UInt64.ofNat (8 * i)) 8 = true := by
  unfold Platform.mapped
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have := hinv.mapped (8 * i + j) (by omega)
  rwa [UInt64.ofNat_add, ← UInt64.add_assoc] at this

/-- Pushing `v` onto a related stack whose new top lies in the register of its height. -/
theorem StackRel.push {s s' : State} {vs : List Value} {v : Value} (h : StackRel s vs)
    (hlen : vs.length < 26) (hv : ValRel v (s'.x (regOf vs.length)))
    (hkeep : ∀ k < vs.length, s'.x (regOf k) = s.x (regOf k)) : StackRel s' (v :: vs) := by
  refine ⟨by simp; omega, fun k hk => ?_⟩
  simp only [List.reverse_cons]
  by_cases hkv : k < vs.length
  · rw [List.getElem_append_left (by simpa using hkv), hkeep k hkv]
    exact h.2 k hkv
  · have : k = vs.length := by simp at hk; omega
    subst this
    simpa using hv

/-! ## The area -/

theorem add_ofNat_add (g : UInt64) (a b : Nat) :
    g + UInt64.ofNat a + UInt64.ofNat b = g + UInt64.ofNat (a + b) := by
  rw [UInt64.add_assoc, UInt64.ofNat_add]

/-- Byte `j` of the area lies below the stack's limit. -/
theorem StoreRel.lt_limit {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) {j : Nat} (hj : j < areaSize cap) :
    (s.x 17 + UInt64.ofNat j).toNat < (s.x 18).toNat := by
  have := h.below
  have := (s.x 18).toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

/-- The store relation holds after code that keeps X17, X18, and the bytes below the stack's
limit. -/
theorem StoreRel.congr {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s s' : State} (h : StoreRel P cap gts st s) (h17 : s'.x 17 = s.x 17)
    (h18 : s'.x 18 = s.x 18)
    (hmem : ∀ a : UInt64, a.toNat < (s.x 18).toNat → s'.mem a = s.mem a) :
    StoreRel P cap gts st s' := by
  have hlt : ∀ j < areaSize cap,
      s'.mem (s.x 17 + UInt64.ofNat j) = s.mem (s.x 17 + UInt64.ofNat j) :=
    fun j hj => hmem _ (h.lt_limit hj)
  have hgl := h.types.length
  have hg := h.glen
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, ?_, ?_, ?_, ?_⟩
  · rw [h17, load64_congr (m := s'.mem) (m' := s.mem) fun k hk =>
      hlt k (by unfold areaSize; omega)]
    exact h.size
  · intro i hi
    rw [h17, load64_congr (m := s'.mem) (m' := s.mem) fun k hk => by
      rw [add_ofNat_add]
      exact hlt _ (by unfold areaSize; omega)]
    exact h.globals i hi
  · intro j hj
    rw [h17, hlt _ (by unfold areaSize; omega)]
    exact h.bytes j hj
  · intro j hj
    rw [h17]
    exact h.mapped j hj
  · rw [h17, h18]
    exact h.below

/-- The store relation holds after code that keeps X17, X18, and the memory. -/
theorem StoreRel.regs {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s s' : State} (h : StoreRel P cap gts st s) (h17 : s'.x 17 = s.x 17)
    (h18 : s'.x 18 = s.x 18) (hmem : s'.mem = s.mem) : StoreRel P cap gts st s' :=
  h.congr h17 h18 fun _ _ => by rw [hmem]

/-! ## Instructions that neither branch nor trap -/

theorem gen_localGet {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.localGet i) = .ok (is, fin)) :
    ∃ (hs : i < 4096) (hi : i < E.localTypes.length), σ.length < 26 ∧
      is = [.ldr (regOf σ.length) 31 ⟨i, hs⟩] ∧ fin = some (E.localTypes[i] :: σ) := by
  unfold genInstr at hg
  by_cases hi : i < E.localTypes.length
  · rw [List.getElem?_eq_getElem hi] at hg
    by_cases hlt : σ.length < 26
    · by_cases hs : i < 4096
      · simp [opReg_ok hlt, slotOf, hs, bind, Except.bind, pure, Except.pure] at hg
        exact ⟨hs, hi, hlt, hg.1.symm, hg.2.symm⟩
      · simp [opReg_ok hlt, slotOf, hs, throw, throwThe, MonadExceptOf.throw, bind,
          Except.bind] at hg
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [he, bind, Except.bind] at hg
  · rw [List.getElem?_eq_none (by omega)] at hg
    simp [throw, throwThe, MonadExceptOf.throw] at hg

theorem sim_localGet (F i : Nat) : InstrSim P code F (.localGet i) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr _ hpc _
  obtain ⟨hs, hi, hlt, rfl, rfl⟩ := gen_localGet hgen
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      have hil : i < (sl.params ++ sl.locals).length := by rw [hinv.count]; exact hi
      simp only [execOne.eq_def, ProofKit.Locals.get_append, List.getElem?_eq_getElem hil]
      have hc : code ms.pc = some (encode (.ldr (regOf σ.length) 31 ⟨i, hs⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hex := step_at (P := P) hc
      simp only [exec, State.xsp_31, State.spAligned, mapped_slot P hinv hi, Bool.and_true,
        hinv.aligned] at hex
      have h18 : ({ ms.setX (regOf σ.length) (load64 ms.mem (ms.sp + UInt64.ofNat (8 * i))) with
          pc := ms.pc + 4 } : State).x 18 = ms.x 18 := by
        rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 _ hlt)]
      refine .inr ⟨_, rfl, _, Reach.single hex, ?_, ?_, ?_, h18, ?_, ?_, ?_,
        hsr.regs (by rw [State.x_withPc, State.x_setX_ne (regOf_ne_17 _ hlt)]) h18
          State.setX_mem⟩
      · simp [hpc, after]
      · simp
      · simp
      · intro a' _; simp
      · refine ⟨StackRel.push hinv.stack (by omega) ?_ ?_, ?_, hinv.count,
          hinv.frame.congr (by simp) h18, Typed.cons ?_ hinv.types, hinv.ltypes⟩
        · rw [hh, State.x_withPc, State.x_setX_same (regOf_lt_31 _ hlt)]
          have := hinv.locals i hil
          rwa [slotAddr, ← ofNat_mul8] at this
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne]
          intro e
          exact absurd (regOf_inj _ hlt k (by omega) e) (by omega)
        · exact hinv.locals.congr (by simp) (by simp)
        · exact hinv.ltypes.getElem hi
      · intro k hk
        rw [State.x_withPc, State.x_setX_ne]
        intro e
        exact absurd (regOf_inj _ hlt k (by omega) e) (by omega)

end LeanExe.A64
