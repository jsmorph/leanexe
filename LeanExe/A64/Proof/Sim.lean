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

/-- The memory outside the frame of `n` locals at `sp` keeps its bytes from `s` to `s'`. -/
def MemFrame (sp : UInt64) (n : Nat) (s s' : State) : Prop :=
  ∀ a : UInt64, ¬ a - sp < UInt64.ofNat (8 * n) → s'.mem a = s.mem a

/-- The values that a branch to `t` carries, the first `t.arity` of `vs`, top first, lie in the
registers of the heights from `t.base` up. -/
structure Kept (t : Ctl) (vs : List Value) (s : State) : Prop where
  len : t.arity ≤ vs.length
  fits : t.base + t.arity ≤ 26
  vals : ∀ j (hj : j < t.arity),
    ValRel (vs[t.arity - 1 - j]'(by omega)) (s.x (regOf (t.base + j)))

/-- What the machine does from `ms` at the code of an instruction or a list, whose end is
`endA`, when Talos gives `r`: `fin` is the height after the code, `none` when its end is
unreachable. -/
def Outcome (E : Env) (ctl : List Ctl) (fin : Option Nat) (endA : UInt64) {α : Type}
    (r : Continuation α) (ms : State) : Prop :=
  match r with
  | .Fallthrough _ sl' => ∃ h', fin = some h' ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = endA ∧
      ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ MemFrame ms.sp E.locals ms ms' ∧
      Inv P E.locals sl' ms' ∧ sl'.values.length = h' ∧ Frame (curBase ctl) ms ms'
  | .Break k _ sl' => ∃ t, ctl[k]? = some t ∧ ∃ ms', Reach P code ms ms' ∧ ms'.pc = t.target ∧
      ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ MemFrame ms.sp E.locals ms ms' ∧
      LocalsRel ms' (sl'.params ++ sl'.locals) ∧ (sl'.params ++ sl'.locals).length = E.locals ∧
      Kept t sl'.values ms' ∧ Frame t.base ms ms'
  | .Return _ vs => ∃ t, ctl.getLast? = some t ∧ ∃ ms', Reach P code ms ms' ∧
      ms'.pc = t.target ∧ ms'.sp = ms.sp ∧ ms'.out = ms.out ∧ MemFrame ms.sp E.locals ms ms' ∧
      Kept t vs ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      ((msg = "unreachable" ∧ ms'.pc = E.trapUnreachable) ∨
        (msg = "integer divide by zero" ∧ ms'.pc = E.trapDiv))
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-- The bases of the enclosing constructs lie at or below the innermost one's. -/
def CtlOk (ctl : List Ctl) : Prop :=
  ∀ t ∈ ctl, t.base ≤ curBase ctl

/-- The simulation of `inst` at fuel `F`. -/
def InstrSim (F : Nat) (inst : Instruction) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (h : Nat) (a : UInt64) (is : List Instr) (fin : Option Nat),
    genInstr E ctl h a inst = .ok (is, fin) → CodeAt code a is → curBase ctl ≤ h → CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E.locals sl ms → sl.values.length = h → ms.pc = a →
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
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hs, hi, hlt, rfl, rfl⟩ := gen_localGet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hil : i < (sl.params ++ sl.locals).length := by rw [hinv.count]; exact hi
      simp only [execOne.eq_def, ProofKit.Locals.get_append, List.getElem?_eq_getElem hil]
      have hc : code ms.pc = some (encode (.ldr (regOf h) 31 ⟨i, hs⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hex := step_at (P := P) hc
      simp only [exec, State.xsp_31, State.spAligned, mapped_slot P hinv hi, Bool.and_true,
        hinv.aligned] at hex
      refine ⟨h + 1, rfl, _, Reach.single hex, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hpc, after]
      · simp
      · simp
      · intro a' _; simp
      · refine ⟨StackRel.push hinv.stack (by omega) ?_ ?_, ?_, hinv.count, ?_, ?_, ?_⟩
        · rw [hh, State.x_withPc, State.x_setX_same (regOf_lt_31 h hlt)]
          have := hinv.locals i hil
          rwa [slotAddr, ← ofNat_mul8] at this
        · intro k hk
          rw [State.x_withPc, State.x_setX_ne]
          intro e
          exact absurd (regOf_inj h hlt k (by omega) e) (by omega)
        · exact hinv.locals.congr (by simp) (by simp)
        · simpa using hinv.aligned
        · simpa using hinv.mapped
        · exact hinv.bound
      · simp [hh]
      · intro k hk
        rw [State.x_withPc, State.x_setX_ne]
        intro e
        exact absurd (regOf_inj h hlt k (by omega) e) (by omega)

end LeanExe.A64
