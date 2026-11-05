import LeanExe.A64.Proof.Relation
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

/-- The memory outside the bytes from the stack's limit `lim` to the end of `n` slots at `sp`
keeps its bytes from `s` to `s'`. -/
def MemFrame (lim sp : UInt64) (n : Nat) (s s' : State) : Prop :=
  ∀ a : UInt64, ¬ a - lim < sp - lim + UInt64.ofNat (8 * n) → s'.mem a = s.mem a

/-- The values that a branch to `t` carries, the first `t.arity` of `vs`, top first, lie in the
registers of the heights from `t.base` up. -/
structure Kept (t : Ctl) (vs : List Value) (s : State) : Prop where
  len : t.arity ≤ vs.length
  fits : t.base + t.arity ≤ 26
  vals : ∀ j (hj : j < t.arity),
    ValRel (vs[t.arity - 1 - j]'(by omega)) (s.x (regOf (t.base + j)))

/-- The machine reaches the stub `tS` of a stack that a frame would overflow from `ms`, with the
UART's output as it was. -/
def Overflows (tS : UInt64) (ms : State) : Prop :=
  ∃ ms', Reach P code ms ms' ∧ ms'.pc = tS ∧ ms'.out = ms.out

/-- The table `callee` names a function, which a call may enter. -/
def HasCalls (callee : Nat → Option (UInt64 × Nat × Nat)) : Prop :=
  ∃ k c, callee k = some c

/-- What the machine does from `ms` at the code of an instruction or a list, whose end is
`endA`, when Talos gives `r`, unless the function may call another and a call's frame would
overflow the stack: `fin` is the height after the code, `none` when its end is unreachable.  SP,
X18, and the UART's output keep their values, and the memory outside the bytes from the stack's
limit to the end of the frame's spill slots keeps its bytes. -/
def Outcome (E : Env) (ctl : List Ctl) (fin : Option Nat) (endA : UInt64) {α : Type}
    (r : Continuation α) (ms : State) : Prop :=
  (HasCalls E.callee ∧ Overflows P code E.trapStack ms) ∨
  match r with
  | .Fallthrough _ sl' => ∃ h', fin = some h' ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = endA ∧
      ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ ms'.x 18 = ms.x 18 ∧
      MemFrame (ms.x 18) ms.sp (E.locals + spillSlots) ms ms' ∧
      Inv P E.locals sl' ms' ∧ sl'.values.length = h' ∧ Frame (curBase ctl) ms ms'
  | .Break k _ sl' => ∃ t, ctl[k]? = some t ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = t.target ∧
      ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ ms'.x 18 = ms.x 18 ∧
      MemFrame (ms.x 18) ms.sp (E.locals + spillSlots) ms ms' ∧
      LocalsRel ms' (sl'.params ++ sl'.locals) ∧ (sl'.params ++ sl'.locals).length = E.locals ∧
      Kept t sl'.values ms' ∧ Frame t.base ms ms'
  | .Return _ vs => ∃ t, ctl.getLast? = some t ∧ ∃ ms', Reach P code ms ms' ∧
      ms'.pc = t.target ∧ ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ ms'.x 18 = ms.x 18 ∧
      MemFrame (ms.x 18) ms.sp (E.locals + spillSlots) ms ms' ∧ Kept t vs ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      ((msg = "unreachable" ∧ ms'.pc = E.trapUnreachable) ∨
        (msg = "integer divide by zero" ∧ ms'.pc = E.trapDiv))
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-- The enclosing constructs, the function's last, with their bases at or below the innermost
one's. -/
structure CtlOk (ctl : List Ctl) : Prop where
  nonempty : ctl ≠ []
  bases : ∀ t ∈ ctl, t.base ≤ curBase ctl

/-- What the machine does from `ms` at the entry of a function of `p` parameters and `r` results,
called on the operand stack `vs`, when Talos's run of the call gives `res`: a success returns to
the address in X30 with SP, X18, and the UART's output as they were, the memory outside the bytes
from the stack's limit up to SP unchanged, and the result, if any, in X0, and a trap reaches the
stub of its code. -/
def CallResult (tU tD : UInt64) (p r : Nat) (vs : List Value) {α : Type} (res : Result α)
    (ms : State) : Prop :=
  match res with
  | .Success vs' _ => ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧
      ms'.x 18 = ms.x 18 ∧ ms'.out = ms.out ∧ MemFrame (ms.x 18) ms.sp 0 ms ms' ∧
      vs'.length = r + (vs.length - p) ∧ vs'.drop r = vs.drop p ∧
      ∀ v ∈ vs'.take r, ValRel v (ms'.x 0)
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      ((msg = "unreachable" ∧ ms'.pc = tU) ∨ (msg = "integer divide by zero" ∧ ms'.pc = tD))
  | .Invalid _ => True
  | .OutOfFuel => True
  | .Thrown _ _ _ => False

/-- `CallResult`, or the machine reaches the stub `tS` of an overflow of the stack. -/
def CallOutcome (tU tD tS : UInt64) (p r : Nat) (vs : List Value) {α : Type} (res : Result α)
    (ms : State) : Prop :=
  Overflows P code tS ms ∨ CallResult P code tU tD p r vs res ms

/-- The simulation of a call of function `k` of `m`, whose entry and numbers of parameters and
results `c` gives, at fuel `g`: from the entry, with the stack's limit in X18 and the top `c.2.1`
values of the operand stack `vs` in X0 upward, the deepest first, the machine does what
`CallOutcome` states of Talos's run of the call. -/
def FunSim (m : Module) (tU tD tS : UInt64) (g k : Nat) (c : UInt64 × Nat × Nat) : Prop :=
  ∀ {α : Type} (st : Store α) (vs : List Value) (ms : State) (hp : c.2.1 ≤ vs.length),
    ms.pc = c.1 → StackOk P ms →
    (∀ i (hi : i < c.2.1),
      ValRel (vs[c.2.1 - 1 - i]'(by omega)) (ms.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩)) →
    CallOutcome P code tU tD tS c.2.1 c.2.2 vs (Wasm.run g m k st vs) ms

/-- The functions of the table `callee` simulate at every fuel below `F` in module `m`, with the
trap stubs `tU`, `tD`, and `tS`. -/
def CallsOk (F : Nat) (m : Module) (callee : Nat → Option (UInt64 × Nat × Nat))
    (tU tD tS : UInt64) : Prop :=
  ∀ k c, callee k = some c → ∀ g < F, FunSim P code m tU tD tS g k c

theorem CallsOk.mono {F G : Nat} {m : Module} {callee : Nat → Option (UInt64 × Nat × Nat)}
    {tU tD tS : UInt64} (h : CallsOk P code F m callee tU tD tS) (hle : G ≤ F) :
    CallsOk P code G m callee tU tD tS :=
  fun k c hk g hg => h k c hk g (by omega)

/-- The simulation of `inst` at fuel `F`. -/
def InstrSim (F : Nat) (inst : Instruction) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (h : Nat) (a : UInt64) (is : List Instr) (fin : Option Nat),
    genInstr E ctl h a inst = .ok (is, fin) → CodeAt code a is → curBase ctl ≤ h → CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E.locals sl ms → sl.values.length = h → ms.pc = a →
      CallsOk P code F m E.callee E.trapUnreachable E.trapDiv E.trapStack →
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
theorem mapped_slot {n : Nat} {sl : Locals} {s : State} (hinv : Inv P n sl s) {i : Nat}
    (hi : i < n) : P.mapped (s.sp + UInt64.ofNat (8 * i)) 8 = true := by
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

/-! ## Instructions that neither branch nor trap -/

theorem gen_localGet {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {i : Nat}
    {is : List Instr} {fin : Option Nat}
    (hg : genInstr E ctl h a (.localGet i) = .ok (is, fin)) :
    ∃ hs : i < 4096, i < E.locals ∧ h < 26 ∧ is = [.ldr (regOf h) 31 ⟨i, hs⟩] ∧
      fin = some (h + 1) := by
  unfold genInstr at hg
  by_cases hi : i ≥ E.locals
  · simp [hi, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h < 26
  · by_cases hs : i < 4096
    · simp [hi, opReg_ok hlt, slotOf, hs, bind, Except.bind, pure, Except.pure] at hg
      exact ⟨hs, by omega, hlt, hg.1.symm, hg.2.symm⟩
    · simp [hi, opReg_ok hlt, slotOf, hs, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind] at hg
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [hi, he, bind, Except.bind] at hg

theorem sim_localGet (F i : Nat) : InstrSim P code F (.localGet i) := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc _
  obtain ⟨hs, hi, hlt, rfl, rfl⟩ := gen_localGet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      have hil : i < (sl.params ++ sl.locals).length := by rw [hinv.count]; exact hi
      simp only [execOne.eq_def, ProofKit.Locals.get_append, List.getElem?_eq_getElem hil]
      have hc : code ms.pc = some (encode (.ldr (regOf h) 31 ⟨i, hs⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hex := step_at (P := P) hc
      simp only [exec, State.xsp_31, State.spAligned, mapped_slot P hinv hi, Bool.and_true,
        hinv.aligned] at hex
      have h18 : ({ ms.setX (regOf h) (load64 ms.mem (ms.sp + UInt64.ofNat (8 * i))) with
          pc := ms.pc + 4 } : State).x 18 = ms.x 18 := by
        rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 h hlt)]
      refine .inr ⟨h + 1, rfl, _, Reach.single hex, ?_, ?_, ?_, h18, ?_, ?_, ?_, ?_⟩
      · simp [hpc, after]
      · simp
      · simp
      · intro a' _; simp
      · refine ⟨StackRel.push hinv.stack (by omega) ?_ ?_, ?_, hinv.count,
          hinv.frame.congr (by simp) h18⟩
        · rw [hh, State.x_withPc, State.x_setX_same (regOf_lt_31 h hlt)]
          have := hinv.locals i hil
          rwa [slotAddr, ← ofNat_mul8] at this
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne]
          intro e
          exact absurd (regOf_inj h hlt k (by omega) e) (by omega)
        · exact hinv.locals.congr (by simp) (by simp)
      · simp [hh]
      · intro k hk
        rw [State.x_withPc, State.x_setX_ne]
        intro e
        exact absurd (regOf_inj h hlt k (by omega) e) (by omega)

end LeanExe.A64
